/// Unified KnowledgeBase — hash-consed terms, facts, indexes, sort lattice.
///
/// One struct maintains everything. Sort relations are facts; entity-of
/// indexes are materialized alongside other indexes.
///
/// See: docs/stage0/rust-term-store-design.md §7, §9 (Layer 0)

pub mod term;
pub mod subst;
pub mod load;
pub mod proof_verify;
pub mod resolve;
pub mod occurrence;
pub mod node_occurrence;
pub mod call_form;
pub mod typing;
pub(crate) mod region;
pub(crate) mod flow_derive;
pub(crate) mod eq_derive;
pub mod defaults;
pub mod op_info;
pub mod op_requirements;
pub mod req_insertion;
pub mod simp_rewrite;
pub(crate) mod body_specialize;
pub mod term_view;
pub mod execute;
pub mod extent;
pub(crate) mod persist_subst;
pub(crate) mod discrim;
#[cfg(test)]
pub(crate) mod test_support;

/// WI-669: body-derived defining-equation types, produced by
/// `KnowledgeBase::op_defining_equations` for the prover/SMT tier.
pub use body_specialize::{DefiningEquation, DefiningGuard};

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::{ResolveResult, ScopeId, SymbolTable, SymbolDef, SymbolKind, Symbol};
use crate::span::{SourceRegistry, SourceSpan};
use term::{Term, TermId, TermStore, TermSource, Var, VarId};
use node_occurrence::NodeOccurrence;
use discrim::SubstTree;
use resolve::BuiltinTag;

// ── Rule handle ─────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct RuleId(u32);

impl RuleId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub fn from_index(index: usize) -> Self {
        RuleId(index as u32)
    }

    pub fn from_raw(raw: u32) -> Self {
        RuleId(raw)
    }

    pub fn raw(self) -> u32 {
        self.0
    }
}

// ── Constraint handle ───────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ConstraintId(u32);

impl ConstraintId {
    pub fn index(self) -> usize { self.0 as usize }
    pub fn raw(self) -> u32 { self.0 }
}

// ── Guard types ─────────────────────────────────────────────────

/// Classification of a guard for optimized checking.
#[derive(Clone, Debug)]
#[allow(dead_code)]
enum GuardKind {
    /// Functional dependency: at most one fact with these key field values.
    /// Pre-check: query discrim tree for existing fact with same key.
    FunctionalDep {
        sort_functor: Symbol,
        key_fields: Vec<Symbol>,
    },
    /// Cardinality bound: count of matching facts <= max_count.
    CardinalityBound {
        sort_functor: Symbol,
        max_count: usize,
    },
    /// General guard: insert, evaluate full LogicalQuery, retract on failure.
    General,
}

/// A registered integrity guard.
struct Guard {
    #[allow(dead_code)]
    id: ConstraintId,
    /// The guard's `LogicalQuery`, carried carrier-agnostically (WI-023): a
    /// `Value::Term` for the hash-consed structural form the loader builds today,
    /// a `Value::Node` occurrence when a guard rides denoted patterns. Read only
    /// through [`TermView`](term_view::TermView), so the engine never assumes a
    /// `TermId`.
    query: crate::eval::value::Value,
    #[allow(dead_code)]
    kind: GuardKind,
    #[allow(dead_code)]
    trigger_sorts: Vec<Symbol>,
    /// Source `constraint` label, for violation diagnostics. `None` if unlabeled.
    label: Option<String>,
}

/// Outcome of evaluating one registered guard in the WI-023 post-load check.
#[derive(Debug, PartialEq, Eq)]
pub enum GuardCheck {
    /// The constraint holds under the current facts.
    Holds,
    /// The constraint is violated. Carries the source label, if any.
    Violated(Option<String>),
    /// The constraint uses a `LogicalQuery` form the shared lowerer cannot
    /// handle — an unknown constructor, or a non-goal-shaped leaf (WI-513).
    /// Carries the source label (if any) and the lowering-error detail. The
    /// loader routes this to a load-BLOCKING error rather than silently loading
    /// with the invariant unenforced.
    Unsupported(Option<String>, String),
    /// WI-628 — the constraint's proof search TRUNCATED at the resolver depth
    /// limit, so it can be neither confirmed nor refuted within budget. Distinct
    /// from `Unsupported` (a malformed form): the form is fine, the SEARCH was
    /// incomplete. The loader routes this to a load-BLOCKING error rather than
    /// silently passing — deciding a constraint from a truncated search is the
    /// unsoundness WI-628 closes. Carries the source label (if any) and a reason.
    Undecidable(Option<String>, String),
}

/// WI-628 — the three-way verdict of evaluating an integrity guard, distinct
/// from a [`execute::LowerError`] (a malformed-constraint failure, the guard's
/// `Err` channel). `Undecidable` is the arm the deferred WI-628 half adds: the
/// guard's proof search TRUNCATED at the depth limit, so an empty / short result
/// cannot be read as `Holds` or `Violated` without deciding from an incomplete
/// search. Carries a static reason for the loud diagnostic.
enum GuardStatus {
    /// The constraint is satisfied (search ran to completion).
    Holds,
    /// The constraint is violated (search ran to completion).
    Violated,
    /// The search truncated at the depth limit; the verdict is undecided.
    Undecidable(&'static str),
}

impl GuardStatus {
    /// Map a DECIDED boolean verdict — one read off a search that ran to
    /// completion — to `Holds`/`Violated`. Centralizes the holds→variant
    /// polarity so the per-guard call sites don't each risk inverting it.
    fn from_holds(holds: bool) -> Self {
        if holds {
            GuardStatus::Holds
        } else {
            GuardStatus::Violated
        }
    }

    /// WI-628 — map a guard whose verdict is "holds iff the search came back
    /// EMPTY" (negation, forall) to a three-way verdict. If the search TRUNCATED
    /// and is empty, the emptiness may be an artifact of the depth cut, so the
    /// verdict is `Undecidable(reason)` rather than a definite refutation. This is
    /// the check that MUST accompany every `is_empty()`-as-verdict read;
    /// centralizing it here (like the `drain_verdict` extraction on the resolver
    /// side) is what keeps a future emptiness-reading guard from forgetting it —
    /// the exact bug class WI-628 closes.
    fn from_emptiness(is_empty: bool, truncated: bool, reason: &'static str) -> Self {
        if truncated && is_empty {
            GuardStatus::Undecidable(reason)
        } else {
            GuardStatus::from_holds(is_empty)
        }
    }
}

// ── Clause kind ─────────────────────────────────────────────────

/// WI-922 — which syntactic form of the kernel language produced a stored
/// clause. Every clause in the KB has exactly one, assigned by the loader site
/// that files it.
///
/// This is NOT the sort a clause is *about*. That question has three
/// correctly-keyed homes of its own — `is_entity_of` (what proposal 010's
/// `sort_query` lowers to), `guards_by_sort` (constraint triggering, via
/// `view_to_trigger_sort`) and `sort_info_index` (the typer's SortInfo lookup)
/// — and none of them is this. Until WI-922 this classification rode a bare
/// `Symbol` field named `sort`, raw-interned per site (`ClauseKind::Fact`),
/// which let three loader sites file a clause under a *user sort's* qualified
/// name instead of a kind and left the field holding two different
/// classifications with nothing able to tell them apart. A closed enum makes
/// that state unrepresentable.
///
/// The nine variants above `Flow` are also *declared*, qualified-only, as
/// kernel meta-sorts by `register_prelude` (`load::KERNEL_META_SORTS`) — that
/// registration exists to keep the names from leaking into user scopes
/// (WI-422/423) and is independent of this enum. `Flow` and `OperationImpl`
/// are deliberately absent from that list: nothing resolves them by name.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum ClauseKind {
    /// A `sort` declaration and its derived entity/subsort clauses.
    Sort,
    /// A sort member (`MemberInfo`) clause.
    Member,
    /// An `operation` declaration.
    Operation,
    /// A `rule` — including the equations `emit_operation_equation` derives
    /// from a body-less operation's defining `=` / `<=>`.
    Rule,
    /// A `fact` — including loader-synthesized metadata facts.
    Fact,
    /// A `requires` clause.
    Requirement,
    /// A `namespace` declaration.
    Namespace,
    /// A doc/description clause.
    Description,
    /// A `constraint` declaration.
    Constraint,
    /// Derived flow clauses (`flow_derive`). Not a kernel meta-sort.
    Flow,
    /// A `provides … { operation … }` implementation clause. Not a kernel
    /// meta-sort.
    OperationImpl,
}

impl ClauseKind {
    /// The kind's spelling — the exact text the pre-WI-922 loader interned as
    /// this clause's key, so diagnostics and persisted output are unchanged.
    pub fn as_str(self) -> &'static str {
        match self {
            ClauseKind::Sort => "Sort",
            ClauseKind::Member => "Member",
            ClauseKind::Operation => "Operation",
            ClauseKind::Rule => "Rule",
            ClauseKind::Fact => "Fact",
            ClauseKind::Requirement => "Requirement",
            ClauseKind::Namespace => "Namespace",
            ClauseKind::Description => "Description",
            ClauseKind::Constraint => "Constraint",
            ClauseKind::Flow => "Flow",
            ClauseKind::OperationImpl => "OperationImpl",
        }
    }
}

impl std::fmt::Display for ClauseKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

// ── Rule entry ──────────────────────────────────────────────────

struct RuleEntry {
    /// The fact/rule head, carrier-agnostic (WI-348 Phase B): `Value::Term`
    /// for the universal hash-consed case, a `Value::Node` for a value fact
    /// carrying a `denoted` occurrence. The many term-only callers read it as a
    /// `TermId` via `rule_head` (which panics on a value head — carrier-agnostic
    /// readers use `rule_head_value` / `TermView`; term-only readers migrate
    /// reactively when that panic actually fires, as `is_equation` did).
    head: crate::eval::value::Value,
    /// WI-246: the rule body — body atoms as `NodeOccurrence` (De Bruijn-encoded
    /// `Expr::Var` leaves), the SOLE body representation now that the term
    /// `body: Vec<TermId>` field is dropped. What the resolver opens as goals
    /// (`with_fresh_vars`) and the typer / `simp_rewrite` walk and rewrite
    /// (uniform with op bodies). Empty for ground facts.
    body_nodes: Vec<Rc<NodeOccurrence>>,
    /// WI-922 — which syntactic form produced this clause. See [`ClauseKind`].
    clause_kind: ClauseKind,
    domain: Symbol,
    meta: Option<TermId>,
    retracted: bool,
    /// Number of de Bruijn-encoded free variables in head+body.
    /// Zero for ground facts. Used by resolver to allocate fresh globals.
    arity: u32,
    /// Pre-DeBruijn Global VarIds in DeBruijn-index order (i.e.
    /// `globals[0]` is the Global VarId that was assigned DeBruijn 0
    /// during rule load). Empty for ground facts. Used by structured-
    /// proof step synthesis to assert step rules in the parent's
    /// variable frame so cited-rule lifts produce `var_<i>` names
    /// aligned with the consumer's preamble declarations.
    globals: Vec<VarId>,
    /// Number of leading DeBruijn slots whose vars are SHARED with a
    /// parent rule's frame. When `shared_arity > 0`, the lift skips
    /// forall-quantifying `var_0..var_{shared_arity-1}` (those refer
    /// to the consumer's already-declared preamble vars); only
    /// `var_{shared_arity}..var_{arity-1}` (the step-introduced new
    /// vars) get emitted as declare-consts.
    shared_arity: u32,
    /// Citation handle for labeled rules. Indexed under
    /// `rules_by_label` so `rule_id_by_qn` resolves a rule by its
    /// label even when the head's functor differs from the label
    /// (e.g. `rule simple_lemma: gte(?x, 3.0) :- ...` — head functor
    /// is `gte`, label is `simple_lemma`). `None` for unlabeled rules
    /// (they remain reachable through `rules_by_functor` on the head).
    label: Option<Symbol>,
    /// WI-582 — typed rule-pattern bounds: `(debruijn_index, bound_type)` pairs
    /// from explicit `?x: T` head annotations. Each entry says "the variable at
    /// this DeBruijn index must, when the rule fires, bind to a value whose
    /// carried type conforms to `bound_type`" (subsort for a sort bound, provides
    /// for a spec bound). Empty for untyped rules — the discrimination tree keys
    /// only on the (structurally identical) head, so the bound rides HERE, off
    /// the structural index (carrier-neutral, M1). Read at fire by
    /// `apply_eq_rules`'s post-match conforms check.
    type_bounds: Vec<(u32, TermId)>,
    /// WI-635: the stored head's `Var::Global`s, in first-occurrence order —
    /// empty when the head is ground. Collected carrier-agnostically at assert
    /// (`push_value_head_entry` → `collect_head_global_vars`) and read two ways,
    /// so the resolver never walks a (potentially large) head per match:
    ///  - `rule_head_has_vars` (`!is_empty`) is the O(1) fact fast-path gate.
    ///  - `with_fresh_vars`' arity-0 legacy path seeds its rename set from this
    ///    cached list instead of re-walking the head every match — and reads no
    ///    term-only `rule_head`, so it is carrier-neutral (a `Value::Node` /
    ///    `Value::Entity` head no longer panics there).
    ///
    /// Meaningful only for the arity-0 fact case the gate consults: a De Bruijn
    /// rule is closed to `Var::DeBruijn` before storage (so this is empty) and is
    /// gated out by `arity > 0` regardless. A non-ground arity-0 fact — the
    /// loader's omitted-field `Term` fills, or a value fact whose children carry
    /// Globals (e.g. an `OperationInfo` whose `type_params` cons-list holds them)
    /// — has a non-empty list and routes through `with_fresh_vars`, freshening
    /// its head vars per match instead of raw-binding their persistent VarIds
    /// into aliasing goals (the arity-0 remnant of the WI-624 leak).
    head_vars: Vec<VarId>,
    /// WI-458 — this head's own source span, or `None` when the loader recorded
    /// none (a synthesized head has no source text). Keyed HERE, on the rule
    /// itself, rather than read back from the `term_spans` side-table: that table
    /// keys on the hash-consed head `TermId`, which two DIFFERENT rules can
    /// share — identical head structure interns once, and `assert_fact` only
    /// dedups when `(term, sort, domain)` ALL match, so same-head/different-domain
    /// facts become distinct rules aliased onto one span (first-write-wins). A
    /// `RuleId` is unique per stored rule, so this cannot cross-file-alias. Set by
    /// the loader right after assert (see `set_rule_head_span`), read by the
    /// typing.rs head-error paths.
    head_span: Option<crate::span::SourceSpan>,
}

/// Immutable, value-facing view of one loaded program clause.
///
/// This intentionally describes source-resident program text: a body, domain,
/// and metadata have no representation in an extent-owned row. It is the
/// inspection seam for callers that need clauses without exposing `RuleId`.
#[derive(Clone, Debug)]
pub struct ProgramClause {
    pub head: crate::eval::value::Value,
    pub body_nodes: Vec<Rc<NodeOccurrence>>,
    /// Which syntactic form produced this clause — see [`ClauseKind`] (WI-922).
    pub clause_kind: ClauseKind,
    pub domain: Symbol,
    pub meta: Option<TermId>,
    /// Leading De Bruijn slots borrowed from a parent rule frame.
    pub shared_arity: u32,
}

impl ProgramClause {
    pub fn is_fact(&self) -> bool {
        self.body_nodes.is_empty()
    }
}

/// A structural program-browse match, without exposing the resident rule slot.
///
/// This is deliberately narrower than the resolver's candidate interface: it
/// is for tools that display matching source clauses (for example CLI
/// `query --match`), not for evaluating facts. Ordinary fact readers use
/// [`KnowledgeBase::read_facts`] / [`KnowledgeBase::read_facts_resolved`] and
/// receive values only. The resolver retains its `RuleId` candidates privately,
/// because it must open the selected rule body.
#[derive(Clone, Debug)]
pub struct ProgramClauseMatch {
    pub clause: ProgramClause,
    pub bindings: subst::Substitution,
}

/// The LIVE RuleId at `key` in a ground-fact dedup index, or `None`.
///
/// `None` covers two different situations that both mean "store it": no entry,
/// and an entry naming a RETRACTED rule. The stale entry is deliberate — `retract`
/// only evicts a key when the RuleId there is its own ([`remove_dedup_entry`]), so
/// a retracted-then-superseded key can linger.
///
/// THE TWO INDEXES DISAGREE ABOUT WHAT TO DO NEXT, and this doc describes only the
/// VALUE path. `assert_fact_value` re-points a stale key with `insert`; the Term
/// path in `assert_rule_nodes` still uses `.or_insert(..)` and says so ("We do not
/// overwrite an existing entry"). On the Term path a stale entry would therefore
/// never be re-pointed, and every later assert of that fact would store another
/// duplicate. That is pre-existing (WI-233) and unreached — the flip that could
/// strand an entry is guarded by a `debug_assert_eq!` in `set_rule_body_nodes`,
/// compiled out in release — but the two indexes should not answer this
/// differently, and this note is here so the next reader sees the asymmetry rather
/// than inferring one rule from the other. Liveness is read bounds-checked, the
/// same rule as [`KnowledgeBase::is_rule_alive`].
///
/// One owner because the two indexes now have different key types (WI-815), so
/// `assert_fact` and `assert_fact_value` would otherwise spell this — and its
/// stale-entry subtlety — twice, as they already do for the removal half.
fn live_dedup_hit<K: std::hash::Hash + Eq>(
    map: &HashMap<(K, ClauseKind, Symbol), RuleId>,
    rules: &[RuleEntry],
    key: &(K, ClauseKind, Symbol),
) -> Option<RuleId> {
    let rid = *map.get(key)?;
    // INDEXED, not `get`: a RuleId sitting in a dedup index that is out of bounds is
    // index CORRUPTION, and the read it replaced panicked on it. Degrading to "not
    // alive" would answer "store it", so the map would silently duplicate that fact
    // forever instead of failing — the silent skip CLAUDE.md forbids. (This is why
    // it is not `KnowledgeBase::is_rule_alive`, whose contract is the opposite: it
    // exists for callers that CANNOT guarantee the id is well-formed.)
    (!rules[rid.index()].retracted).then_some(rid)
}

/// Drop `key`'s entry from a ground-fact dedup index, but ONLY when `id` is the
/// RuleId currently sitting there.
///
/// The rid guard is the whole point and is easy to forget: a fact that was
/// retracted and then re-asserted holds a DIFFERENT RuleId at the same key, and
/// evicting it would un-dedup a live fact. WI-815 gave the two indexes different
/// key types (`fact_dedup` on `TermId`, `value_fact_dedup` on `GoalKey`), which
/// would otherwise mean spelling the guard twice in `retract`; one generic owner
/// keeps them from drifting.
fn remove_dedup_entry<K: std::hash::Hash + Eq>(
    map: &mut HashMap<(K, ClauseKind, Symbol), RuleId>,
    key: (K, ClauseKind, Symbol),
    id: RuleId,
) {
    if let std::collections::hash_map::Entry::Occupied(e) = map.entry(key) {
        if *e.get() == id {
            e.remove();
        }
    }
}

/// Collect the ground `TermId` leaves reachable in a value (WI-348 Phase B), for
/// the value-fact refcount helpers. Recurses through `Value::Entity` / `Tuple`
/// children directly and through a `Value::Node` occurrence via `TermView`.
fn collect_value_ground_terms_into(
    kb: &KnowledgeBase,
    v: &crate::eval::value::Value,
    out: &mut Vec<TermId>,
) {
    use crate::eval::value::Value;
    match v {
        Value::Term { id: t, .. } => out.push(*t),
        Value::Entity { pos, named, .. } | Value::Tuple { pos, named, .. } => {
            for c in pos.iter() {
                collect_value_ground_terms_into(kb, c, out);
            }
            for (_, c) in named.iter() {
                collect_value_ground_terms_into(kb, c, out);
            }
        }
        Value::Node(occ) => collect_occ_ground_terms_into(kb, occ, out),
        _ => {}
    }
}

/// Walk a `Value::Node` occurrence through `TermView`, pushing every ground
/// `TermId` child and recursing into nested value / occurrence children. A
/// non-`Functor` head (Const / Ref / Ident / Opaque) carries no ground child.
fn collect_occ_ground_terms_into(
    kb: &KnowledgeBase,
    occ: &std::rc::Rc<node_occurrence::NodeOccurrence>,
    out: &mut Vec<TermId>,
) {
    use term_view::{TermView, ViewHead, ViewItem};
    let pos_arity = match occ.head(kb) {
        ViewHead::Functor { pos_arity, .. } => pos_arity,
        _ => return,
    };
    for i in 0..pos_arity {
        match occ.pos_arg(kb, i) {
            Some(ViewItem::Term(t)) => out.push(t),
            Some(ViewItem::Value(c)) => collect_value_ground_terms_into(kb, c, out),
            Some(ViewItem::Owned(c)) => collect_value_ground_terms_into(kb, &c, out),
            Some(ViewItem::Node(o)) => collect_occ_ground_terms_into(kb, &o, out),
            None => {}
        }
    }
    for sym in occ.named_keys(kb) {
        match occ.named_arg(kb, sym) {
            Some(ViewItem::Term(t)) => out.push(t),
            Some(ViewItem::Value(c)) => collect_value_ground_terms_into(kb, c, out),
            Some(ViewItem::Owned(c)) => collect_value_ground_terms_into(kb, &c, out),
            Some(ViewItem::Node(o)) => collect_occ_ground_terms_into(kb, &o, out),
            None => {}
        }
    }
}

// ── Sort kind ───────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SortKind {
    Sort,
    Enum,
}


// ── Sort operations table ───────────────────────────────────────

/// WI-240 — per-impl-sort operations table. For each impl sort `S`
/// with a `fact Spec[bindings]`, maps each of `Spec`'s declared op
/// short names to the symbol the runtime should invoke: `S.<op>` when
/// the impl overrides with a runnable body, otherwise the spec op
/// itself (`Spec.<op>` — resolved via the spec's rewrite rule or a
/// registered builtin at runtime).
///
/// Built once at load time by `load::build_sort_ops_table` (and, for the
/// `eq_dispatch` field below, `load::build_eq_dispatch_index` right after), once all
/// `SortProvidesInfo` / `OperationInfo` facts are asserted. Dispatch
/// consumers (the typer's `resolve_at_goal`, the eval's
/// `apply_within`) read it via [`KnowledgeBase::sort_ops_lookup`] — a
/// direct table lookup, replacing the prior
/// `format!("{impl_qn}.{op}").or_else(spec_qn)` string-concatenation
/// fallback. See `docs/design/operation-call-model.md` §"Putting it
/// together: dispatch end-to-end".
#[derive(Default, Debug)]
pub(crate) struct SortOpsTable {
    /// impl sort symbol → (op short-name symbol → target op symbol).
    by_impl: HashMap<Symbol, HashMap<Symbol, Symbol>>,
    /// WI-616 — semantic-equality dispatch index: value-head functor →
    /// the carrier's `eq` override op. Built by `load::build_eq_dispatch_index`
    /// for every sort with exactly one `eq` supplier — its own member
    /// (`typing::carrier_own_op` filters: not the `PartialEq.eq` spec op, parented
    /// by the sort itself), a retroactive instance fact's op binding, or (WI-837) a
    /// witness sort's; two DISTINCT suppliers is a load error, not a silent pick.
    /// `load::EqDispatchIndex` owns that criterion. Keys are the
    /// sort's entity constructors and its SELF-RETURNING ops (the shapes its
    /// values are made of — `Set.insert`/`Set.empty`; a non-self-returning
    /// op like `Map.get` returns a DIFFERENT sort's value and must not key
    /// dispatch here). Read per `eq`/`neq` goal on the structurally-unequal
    /// path (`resolve.rs` `sem_eq_dispatch_target`) — one hash probe, no
    /// string hashing, no KB scans.
    eq_dispatch: HashMap<Symbol, Symbol>,
}

// ── KnowledgeBase ───────────────────────────────────────────────

/// WI-835 — one written parameterized type instantiation (`Map[K = Float, V =
/// Int64]`), as the post-load use-site checks need it: the base sort, the
/// bindings that name a CARRIER, and where the base name was written.
///
/// Recorded by the type lowerings that have a `TypeExpr::Parameterized` arm —
/// `type_expr_to_child` (ordinary type positions) and `sort_binding_to_value` (a
/// type written as a binding VALUE inside a `requires` / `provides` clause). Both
/// record, because "the sole type lowering" is not one function: `type_expr_to_value`'s
/// doc says it is, but the spec-clause path builds its own `SortView` and never
/// routes through it, so a `requires Spec[C = Map[K = Float]]` escaped a check
/// keyed on the ordinary lowering alone.
///
/// The BINDINGS are recorded, not the assembled type term, for two reasons. The
/// lowering has already mapped positional arguments onto declared parameter names,
/// so a consumer that re-decomposed the term would duplicate that mapping (and its
/// positional half would be dead code, since the assembled term carries named args
/// only). And a DENOTED-bearing instantiation (`Buf[T = Int64, N = 3]`) has no
/// ground term at all — it rides as a `Value::Node` — yet its non-denoted siblings
/// still bind carriers: recording the term dropped `K = Float` from `Map[K = Float,
/// V = Buf[T = Int64, N = 3]]` entirely, so an unrelated value-in-type argument
/// silently disabled the lawful-key check.
#[derive(Clone, Debug)]
pub(crate) struct ParameterizedSite {
    /// The sort being instantiated (`anthill.prelude.Map`).
    pub base: Symbol,
    /// Bindings whose value is a ground TYPE, by DECLARED parameter name
    /// (positionals already mapped). A `denoted` binding is omitted: it stands a
    /// VALUE in a type-argument position, so it carries no `requires Spec[param]`
    /// obligation — omitting just that binding, rather than the whole site, is
    /// what keeps its carrier-bound siblings checked.
    pub bindings: SmallVec<[(Symbol, TermId); 2]>,
    /// Where the base name was written, for a `path:line:col` diagnostic. Carries
    /// the `SourceId`: byte offsets alone repeat across files.
    pub span: SourceSpan,
}

/// WI-840/WI-841 (058 §4.7) — one NAMED requirement slot of an operation or a sort:
/// `requires O: Ord[T = E]`. See [`KnowledgeBase::named_requirement_slots`] for the
/// two lists `slot` indexes and why `spec_base` is recorded beside it rather than
/// derived from it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NamedRequirementSlot {
    /// The name the author gave the slot — an ordinary type parameter of the owner
    /// by the time this is recorded, so it is also a call-bracket key (§4.2 rule 1).
    pub binder: Symbol,
    /// The slot's POSITION among the owner's `requires` items, in source order.
    pub slot: usize,
    /// The base sort of the spec the slot demands (`Ord` in `O: Ord[T = E]`).
    /// `None` only when the declaration's spec had no resolvable base — a shape the
    /// converter already refused (`requires <name>: <not a spec>`), kept as an
    /// option rather than a panic so a malformed declaration still loads its
    /// siblings.
    pub spec_base: Option<Symbol>,
}

pub struct KnowledgeBase {
    // Term storage (hash-consed, refcounted)
    pub(crate) terms: TermStore,
    pub(crate) symbols: SymbolTable,

    /// WI-628 — TEST-ONLY override of the CLOSED carrier-`eq`/`neq` sub-proof depth
    /// budget ([`Self::prove_rule_predicate`], default [`Self::DEFAULT_SEM_EQ_SUB_DEPTH`]).
    /// Production always uses the const (a fixed, generous budget — 100_000, so a
    /// legitimate compare truncates only for very large operands, degrading to
    /// UNDECIDED, never a wrong verdict); this `cfg(test)` field lets a unit test
    /// force truncation in a handful of steps instead of a 100k-step loop, WITHOUT
    /// widening production KB's mutable surface with a soundness-critical knob.
    #[cfg(test)]
    pub(crate) sem_eq_sub_depth: usize,

    // Rules (facts are rules with empty body)
    rules: Vec<RuleEntry>,

    // Indexes — all maintained atomically by assert/retract.
    //
    // WI-922 — there is deliberately no index on [`RuleEntry::clause_kind`].
    // One was maintained from the first commit until WI-922, as
    // `by_sort: HashMap<Symbol, Vec<RuleId>>`, and its name was the original
    // defect: the stage-0 design (`docs/rust-term-store-design.md`) specified it
    // as "all facts of a given sort (including its entities)" and proposal 010
    // planned a user-facing `by_sort(Color)` on top of it, but the loader — its
    // only producer — never filed a clause under a sort. It files the clause
    // KIND, so the index answered "which clauses are of kind K" from the first
    // commit onward while its name promised something else.
    //
    // Naming it honestly is what showed it should not exist. A kind is a
    // FILTER, not a selector: of its readers, `rule_heads_for_sort` selects on
    // `by_domain` (far more selective) and merely filters on the kind; the proof
    // tests want `rules_by_functor`; and the last one, `hint_cites_for`, runs
    // once per Z3 dispatch and discriminates on a `hint` meta flag anyway. One
    // cold caller does not pay for a map pushed at every assert and
    // retain-scanned at every retract. Filtering a live-clause walk on a `Copy`
    // enum is the cheaper and clearer answer. The sort question, meanwhile, has
    // three correctly-keyed homes of its own — `is_entity_of` (what proposal
    // 010's `sort_query` lowers to), `guards_by_sort` (constraint triggering,
    // via `view_to_trigger_sort`) and `sort_info_index` (the typer's SortInfo
    // lookup) — and none of them was ever this.
    rules_by_functor: HashMap<Symbol, Vec<RuleId>>,
    by_domain: HashMap<Symbol, Vec<RuleId>>,
    rules_by_label: HashMap<Symbol, Vec<RuleId>>,

    /// WI-812: per-functor count of currently-indexed BODIED rules (non-facts) —
    /// maintained in lockstep with `rules_by_functor` at each of its three
    /// mutation sites (`push_value_head_entry`, `retract`, `unindex_functor`).
    /// Backs the O(1) [`Self::has_bodied_rule`] gate that [`Self::read_facts`]
    /// reads for its blanket bodied-rule refusal, so the common (pure-table) read
    /// proves the ABSENCE of a bodied rule with one map lookup instead of a
    /// `rules_by_functor` bucket scan + per-row `is_fact`. A COUNT (not a
    /// bool/set) so dropping one of several bodied rules under a functor leaves
    /// the flag correctly set. Entries at zero are removed, so the map holds only
    /// functors that currently have ≥1 bodied rule.
    bodied_rule_counts: HashMap<Symbol, u32>,

    // Entity-of indexes: entity → parent sort (1-level, non-transitive).
    // Materialized indexes for EntityOf(entity, parent) facts.
    sort_entities: HashMap<Symbol, Vec<Symbol>>,   // sort → its entity constructors (WI-697 finished: by SYMBOL)
    entity_parent: HashMap<Symbol, Symbol>,         // entity ctor SYMBOL → its parent sort NAME (WI-697, both halves)
    sort_info: HashMap<Symbol, SortKind>,

    // Discrimination tree index for structural term matching
    discrim: SubstTree<RuleId>,

    // WI-233: dedup index for ground facts (body-empty rules) with a
    // `Value::Term` head. Keyed by (head, clause_kind, domain) so `assert_fact`
    // can short-circuit on a duplicate in O(1) instead of scanning
    // `by_clause_kind[kind]` linearly. Pre-WI-233 the scan averaged ~180 entries
    // per call on a stdlib load; this index brings it to a single hash lookup.
    //
    // A hash-consed `TermId` IS the structural identity of a `Term` head, so this
    // stays the O(1) key it has always been. A `Node`/`Entity` head has no such
    // id and keys `value_fact_dedup` instead (WI-815).
    fact_dedup: HashMap<(TermId, ClauseKind, Symbol), RuleId>,

    /// WI-815: the same dedup index for a `Node`/`Entity`-carrier ground-fact
    /// head, keyed by its carrier-agnostic [`GoalKey`] structural fingerprint.
    ///
    /// THE RULE: the two spaces are DISJOINT — a `Value::Term` head and a
    /// structurally-identical `Node`/`Entity` head do NOT dedup against each other,
    /// where pre-WI-815 they could (the value key was materialized into
    /// `fact_dedup`). That is deliberate, not incidental, and is pinned by
    /// `wi815_the_two_key_spaces_are_disjoint`. It is sound in the only direction
    /// that matters: splitting can only LOSE a dedup (a miss — the duplicate is
    /// stored), never collapse two facts into one.
    ///
    /// Keeping ONE space would have meant fingerprinting every `Term` head too,
    /// trading an O(1) interned id for a walk plus a `Vec` alloc on the load path
    /// — and a hash-consed `TermId` already IS a `Term`'s structural identity, the
    /// case CLAUDE.md's representation note names as where hash-consing pays.
    ///
    /// Evidence that the split costs nothing in practice (a corpus-wide
    /// cross-carrier hit count of zero) is in
    /// `docs/design/value-facts-carrier-agnostic-resolver.md` §Delivered, not
    /// restated here — it is a measurement of one moment, and the rule above is
    /// what a maintainer must not break. See [`Self::value_fact_dedup_key`].
    value_fact_dedup: HashMap<(term_view::GoalKey, ClauseKind, Symbol), RuleId>,

    // WI-169: structural-dedup memo for synthesized conjunction-rules
    // (`_synth_N(?vars) :- body`, minted by `synthesize_conjunction_rule` when
    // a multi-goal disjunction/negation branch is lowered for a query). Keyed
    // on the body's structural fingerprint (`Vec<SynthKey>`: interned symbols +
    // De Bruijn-style positional var indices, preserving variable sharing), so
    // a repeated multi-goal query reuses one synth rule instead of appending a
    // fresh rule slot + symbol + discrim entry per execution — bounding the
    // synth population by #distinct-bodies, not #queries. The key is
    // storage-neutral (no `TermId` slot identity), so it can never dangle. A
    // synth rule is a permanent lowering artifact (never retracted), so this
    // memo never goes stale and needs no invalidation; like `fact_dedup` it
    // must be reset alongside `rules` by any future KB clone/reset.
    synth_rule_memo: HashMap<Vec<execute::SynthKey>, Symbol>,

    // Builtin dispatch: functor symbol → builtin tag
    builtins: HashMap<Symbol, BuiltinTag>,

    // Entity field registry: functor symbol → ordered field names.
    // Populated during load_entity, used by convert_term for partial named-arg expansion.
    pub(crate) entity_fields: HashMap<Symbol, Vec<Symbol>>,

    // Set of functor symbols that are constructors (entities with a parent sort).
    // Populated by register_entity_of, used by is_constructor_symbol for O(1) lookup.
    constructor_symbols: HashSet<Symbol>,

    // Variable counter for fresh VarId allocation
    next_var: u32,

    // Base substitution for each sort: maps all params + operations to themselves.
    // Computed by resolve_instantiations() after loading.
    // Key: sort functor symbol. Value: list of (slot_name, Ref(slot_name)) pairs.
    sort_base_subst: HashMap<Symbol, Vec<(Symbol, TermId)>>,

    // Well-known sort terms (cached for future layers)
    #[allow(dead_code)]
    sort_sort: Option<TermId>,
    #[allow(dead_code)]
    entity_of_sort: Option<TermId>,

    // Guards — integrity constraints checked on assert
    guards: Vec<Guard>,
    guards_by_sort: HashMap<Symbol, Vec<usize>>,

    /// WI-251 — span side-table keyed by stored term TermId. Populated
    /// by `load.rs::create_occurrence_ex` for every expression /
    /// fact-head / rule-head term registered during load. Replaces the
    /// legacy `the legacy occurrence by-term index(t).first().span(...)` lookup
    /// used by typing.rs error-formatting paths.
    pub(crate) term_spans: HashMap<TermId, crate::span::SourceSpan>,
    /// WI-251 — first-encountered span keyed by functor symbol.
    /// Populated alongside `term_spans` so typing.rs can recover a
    /// representative span for an operation / sort / entity when only
    /// its symbol is in hand (e.g. `check_operation_bodies`'s
    /// span-by-op-sym lookup).
    pub(crate) functor_spans: HashMap<Symbol, crate::span::SourceSpan>,

    /// WI-242 — value-typed operation bodies keyed by operation symbol.
    /// WI-305: this side-table is now the SOLE store of operation bodies — the
    /// `OperationInfo.body` / `OperationImpl.body` fact fields were dropped, and
    /// the term handle is no longer built/stored. anthill code reaches a body via
    /// the `anthill.reflect.operation_body` builtin (which reads this table).
    /// See `docs/design/occurrence-as-value-type.md`.
    ///
    /// WI-348 / **WI-370**: deliberately NOT collapsed into the `OperationInfo`
    /// value fact (which would complete the "everything is facts" model). The
    /// body is keyed data (`Symbol` → body), but it is *also* an `Expr`
    /// occurrence whose control-flow forms (`let`/`if`/`match`) read `Opaque` in
    /// `occ_head`. The discrimination tree indexes a fact head's *full* nested
    /// structure, so a fact-resident body would force the insert walk down into
    /// that `Expr` — building a per-body structural MIRROR in the trie that no
    /// query prunes on (the body is never a discriminator; ops are found by
    /// `name`), needing `occ_head` to mirror the whole `Expr` enum, and risking
    /// deep recursion. Doing the collapse *cleanly* — body in the fact, still
    /// shape-queryable — needs a **custom-unification / custom-search hook at a
    /// discrim node** (delegate the body subterm to on-demand `TermView` unify
    /// instead of trie descent): tracked as **WI-370**. Until that lands, the
    /// body stays here, reachable relationally via `operation_body`.
    ///
    /// WI-656 — the body now rides in a unified per-operation `OperationRecord`
    /// alongside the operation's cached `OpSignature`, so the typer's signature
    /// lookup (`op_info::lookup_operation_info`) is an O(1) map hit instead of an
    /// O(N_ops) scan of the `OperationInfo` facts. The three body accessors
    /// (`op_body_node` / `set_op_body_node` / `op_bodies_iter`) are unchanged in
    /// signature; they just read/write `record.body`.
    pub(crate) op_records: HashMap<Symbol, op_info::OperationRecord>,

    /// WI-727 (proposal 056) — the VARIADIC CAPTURE parameter of each operation that
    /// declares one: `op_sym → the name symbol of its `...args: R` capture parameter`.
    /// Populated by the loader, read O(1) by the typer's argument matching
    /// (`check_apply_iter`) to collect leftover named arguments into the capture record
    /// rather than rejecting them. Absent ⇒ the op has no capture.
    ///
    /// A dedicated side-table (mirroring `op_records` / `sort_alias_index`) rather than a
    /// marker field on the `OperationInfo` fact's per-param `FieldInfo`: `FieldInfo` is
    /// SHARED with entity fields (a capture marker is meaningless there), and `params`
    /// threads through many typer sites as `Vec<(Symbol, Value)>` — a fact-backed flag
    /// would either leak into that shape or need a parallel read anyway. The `...` marker
    /// is loader-only (no runtime/persistence surface — the printer renders no operation
    /// declarations), so the side-table needs no fact backing to survive.
    pub(crate) op_capture_params: HashMap<Symbol, Symbol>,

    /// WI-840 (proposal 058 §4.7) — the NAMED requirement slots declared by an
    /// operation or a sort: `owner → [(binder, slot position)]`, in source order.
    ///
    /// `requires O: Ord[T]` is TWO facts about one declaration. The first — that `O`
    /// is a type PARAMETER of the owner — needs no table: the converter desugars the
    /// binder into the ordinary parameter machinery, so `O` is addressable in type
    /// position and at a call bracket exactly like any `[T]`. This table carries the
    /// second: WHICH requirement slot that parameter names.
    ///
    /// A POSITION, not the spec. A slot's identity is positional throughout
    /// (`requirement_at_sort(node, k)`), and phase 1 adds a name where one was
    /// missing rather than re-keying the projection path (§4.7 wrinkle 3) — and the
    /// spec would not discriminate the case that motivates naming at all: the two
    /// slots of `requires plus: Monoid[T], times: Monoid[T]` hash-cons to ONE term.
    ///
    /// **WHICH list `k` indexes, exactly — it is not the same list at both levels,
    /// and one obvious candidate is measurably wrong.** In both cases it is the
    /// SOURCE order of the owner's `requires` items, which is preserved by:
    ///
    /// * an OPERATION — the flattened requirement GOALS, i.e. what
    ///   `op_requires_entries` enumerates (value preconditions included, since they
    ///   occupy positions in the written list too). NOT `OperationInfo.requires`,
    ///   which holds CLAUSES: `convert_clause_list_with_extra` collapses a multi-goal
    ///   clause into one `conjunction(…)`, so the two named slots of the example
    ///   above index a list of length 1 there.
    /// * a SORT — `SortInfo.requires`, built by `load_sort_with_body`'s walk over the
    ///   same `s.items` in the same order. **NOT the `SortRequiresInfo` FACT order**:
    ///   `resolve_requires_bindings` RETRACTS and re-asserts every requirement whose
    ///   op bindings it completes, moving it to the end of the functor index — so on
    ///   a sort whose requirements are not all completed the fact order is a
    ///   permutation of the source order (measured: `requires O: Ord[T = E]` followed
    ///   by a parameterless `requires Marker` comes back `Marker, Ord`). Anything
    ///   reading `direct_requires` must map through `SortInfo.requires`, not assume
    ///   the two agree.
    ///
    /// A side-table rather than a field on those facts, for `op_capture_params`'
    /// reasons: the record is loader-produced and typer-consumed, with no runtime or
    /// persistence surface (the printer renders no declarations). Putting the binder
    /// ON the requirement instead — a third `SortRequiresInfo` field, which the
    /// retract/re-assert would carry — is the coordinate-free alternative, and the
    /// one to reach for if phase 2 finds the mapping above load-bearing rather than
    /// incidental.
    ///
    /// **WI-841 found it load-bearing, and took the coordinate-free half of that
    /// advice without the schema change**: selection needs to know a slot's SPEC (to
    /// pin a provider for it) and which slots are *anonymous* (rule (2)'s candidate
    /// set), and deriving either from `slot` would have made the typer re-do the
    /// position→list mapping above — silently wrong at the sort level, where the
    /// list a typer has in hand (`direct_requires_chain`) is the FACT order. So
    /// [`NamedRequirementSlot`] records the spec base BESIDE the position, written
    /// where both are in hand (the loader). The position stays and is now RECORDED BUT
    /// UNREAD — no production code consults it (only WI-840's own test, which pins the
    /// coupling and its divergence from the fact order so the warning above cannot go
    /// stale). Kept because the projection path is positional (§4.7 wrinkle 3) and
    /// phases 3-4 are where a name would have to reach it; it is not load-bearing
    /// today, and this comment says so rather than implying a reader that exists.
    pub(crate) named_requirement_slots: HashMap<Symbol, Vec<NamedRequirementSlot>>,

    /// WI-659 — the SortAlias resolution index (source sort → alias target), built
    /// once at type-check start by `typing::build_sort_alias_index`. `None` until
    /// built; while `None`, `resolve_sort_alias` falls back to its (slower) scan.
    /// Made `resolve_sort_alias` — the #1 `type_check_sorts` hotspot after WI-656 —
    /// an O(1) lookup instead of a double linear scan of every SortAlias fact.
    pub(crate) sort_alias_index: Option<crate::kb::typing::SortAliasIndex>,

    /// WI-660 — the SortProvidesInfo (provider/coherence) index: providers keyed
    /// BOTH by canonical spec-base symbol AND by canonical carrier symbol, built once at
    /// type-check start by `typing::build_provides_index`. Replaces the per-call
    /// linear scans of every provides fact at the dispatch/coherence sites (the SAME
    /// `rules_by_functor` antipattern as `op_records`/`sort_alias_index`). A
    /// MANY-TO-MANY relation (carrier × spec), so TWO `SymbolKeyedFactIndex` buckets
    /// (WI-661), both keyed by `canonical_sort_sym` (WI-672 re-keyed the carrier
    /// direction from a short-name bucket to the canonical carrier symbol; consumers
    /// compare by `canonical_sort_sym`, not `same_symbol` — see `ProvidesIndex`).
    ///
    /// SOUND BUILD-ONCE — NO per-mutation invalidation. `SortProvidesInfo` is marked
    /// `constant` (`fact_monotonicity`, reflect.anthill; proposal 053 / WI-665), so
    /// the WI-666 eval guard makes a runtime `Store.persist`/`retract` of it a LOUD
    /// error — the relation cannot change after load, so the index read AT RUNTIME
    /// (`sort_provides` from the resolver's simp guard, `provider_spec_view_bindings`
    /// from eval dispatch) can never go stale (this is what closed the WI-607 ABA
    /// hole that once blocked this WI). During LOAD it tracks the mutating relation
    /// explicitly — it is `Some` only while the relation is FROZEN and `None` (consumers
    /// scan live) across every load-time mutation window: reset to `None` at
    /// `load_phase_inner` start (like `sort_alias_index`) and again just before
    /// `eq_derive::run` (which reads the relation WHILE asserting derived composite
    /// `NonEq`/`PartialEq`), and (re)built by `build_provides_index` at `type_check_sorts`
    /// start (the hot consumer) and again right after `eq_derive::run`. `None` until
    /// first built; while `None`, every consumer falls back to the live scan.
    pub(crate) provides_index: Option<crate::kb::typing::ProvidesIndex>,

    /// WI-671/WI-672 — the SortInfo (per-sort reflect metadata) index: each sort's fact
    /// keyed by the CANONICAL sort symbol (`canonical_sort_sym`) of its `name` field, in
    /// a shared `SymbolKeyedFactIndex` (WI-661), built once at type-check start by
    /// `typing::build_sort_info_index`. Replaces the
    /// per-call linear scan of every SortInfo fact at the four per-query keyed lookup
    /// sites (the SAME `rules_by_functor` antipattern as `op_records`/`sort_alias_index`/
    /// `provides_index`), the hottest being `find_sort_info`, called once PER SORT in
    /// the `type_check_sorts` loop (O(sorts²) before this).
    ///
    /// Keyed by CANONICAL sort symbol (WI-672, re-keyed from the former short name).
    /// `SortInfo.name` is always a resolved sort functor (`emit_sort_info` emits
    /// `Term::Ref(sort_functor)`), so its canonical symbol IS the sort identity — an
    /// exact key. This de-conflates two DISTINCT sorts that merely share a last segment
    /// (a top-level `sort Ring` vs `anthill.prelude.algebra.Ring`), which the former
    /// short-name bucket + `same_symbol` re-filter silently merged. The two consumers
    /// that compared `name` via `same_symbol` now compare via `canonical_sort_sym` (no
    /// short-name / last-segment matching); the two that used raw `==` are unchanged
    /// (raw `==` within a canonical bucket returns the same exact fact).
    ///
    /// SOUND BUILD-ONCE — no per-mutation invalidation, no `constant` runtime guard.
    /// `SortInfo` is frozen well before `type_check_sorts` and cannot go stale — no
    /// eq_derive null-then-rebuild pair (unlike `provides_index`). Reset to `None` at
    /// `load_phase_inner` start for incremental loads; `None` until first built, and
    /// while `None` every consumer falls back to the live scan.
    ///
    /// WI-1008 — "asserted ONLY by `emit_sort_info`, never retracted or re-asserted" was
    /// how that freeze used to be argued, and it no longer holds:
    /// `load::merge_secondary_entry_operations` retracts and re-asserts a sort's record to
    /// add the operations its SECONDARY ENTRIES declare (059 R2). The freeze survives on a
    /// narrower claim — that writer runs inside `resolve_instantiations`, strictly before
    /// the build — and it drops this index when it rewrites, which is what covers the
    /// `load` entry point, where the `load_phase_inner` reset never runs. THE STANDING
    /// RULE for any future writer: drop the index, because a retracted RuleId left in a
    /// bucket is SERVED, not detected — `is_fact` and `fact_head_named_args` read a
    /// retracted slot happily, so the failure is a stale answer rather than an error.
    pub(crate) sort_info_index: Option<crate::kb::typing::SymbolKeyedFactIndex>,

    /// Proposal 039 / WI-084 — a term-level constant's DECLARED TYPE, keyed by
    /// its `SymbolKind::Const` symbol, as a carrier-agnostic `Value`. Read by
    /// the typer to type a bare const reference (fold-free: only the declared
    /// type, never the value). A dedicated table — NOT folded into a reflect
    /// `ConstInfo` fact in this phase; that consolidation can come with the
    /// resolution/typing phase if reflection needs it.
    pub(crate) const_types: HashMap<Symbol, crate::eval::value::Value>,

    /// Proposal 039 / WI-084 — a term-level constant's defining-expression body,
    /// keyed by its `SymbolKind::Const` symbol. A SEPARATE table from `op_bodies`
    /// on purpose: `op_bodies_iter` is scanned by operation-only passes (e.g.
    /// `req_insertion`), which must not see const bodies. Bodyless (host-supplied)
    /// consts have no entry. Folding the body to a value is a later phase.
    pub(crate) const_bodies: HashMap<Symbol, Rc<NodeOccurrence>>,

    /// WI-443 — true once the loader has built any `dot_apply` expression.
    /// The typer's tree-reassembly gate reads it: a DotApply is ALWAYS
    /// rewritten by the typer (to the dispatched call), so its ancestors
    /// must be reassembled for the rewrite to reach the stored body (and
    /// thus eval) even when no `[simp]` equation is loaded.
    pub(crate) has_dot_applies: bool,

    /// WI-646 — cached O(1) answer to "does this KB hold ANY directional
    /// (`[simp]`/`[unfold]`) equation under the `eq` or `unify` functor?" — the
    /// gate [`Self::has_directional_rewrite`] reads so the resolver's
    /// `apply_eq_rules` short-circuits a no-rewrite KB on the SLD hot path
    /// WITHOUT the per-call `rules_by_functor` bucket scan (2 `Vec` allocs). It
    /// mirrors `equation_is_directional_rewrite` over BOTH functors, so it is the
    /// CORRECT gate — unlike the `[simp]`-only/`eq`-only `has_simp_equations`,
    /// whose narrowness made WI-643's naive gate skip unfold-only / `<=>`-only
    /// KBs. `None` = not yet computed / invalidated; recomputed lazily on the next
    /// gate read. Set to `None` wherever the `eq`/`unify` functor buckets (or a
    /// member's retracted/meta state) change: `push_value_head_entry`, `retract`,
    /// `unindex_functor`.
    simp_gate_cache: Option<bool>,

    /// WI-627: the resolved `anthill.prelude.PartialEq.eq` / `anthill.kernel.unify`
    /// connective symbols, cached at [`Self::register_builtin_tags`] time
    /// (re-synced in [`Self::resolve_builtins`]) so
    /// [`Self::is_equality_connective_functor`] — on the resolver's per-candidate
    /// `is_equation` hot path — is an O(1) field read, not two long-string
    /// `by_qualified_name` lookups per call. `None` in a prelude/kernel-less unit
    /// KB (never registers builtins); that KB's only equation shape is a bare
    /// `intern("eq")`/`intern("unify")` head, matched by short name in the
    /// fallback. The two symbols are load-stable (the `by_qualified_name` entry is
    /// reused, never re-minted — verified for the full stdlib load), so the cache
    /// never goes stale.
    eq_connective_sym: Option<Symbol>,
    unify_connective_sym: Option<Symbol>,

    /// WI-657(6): the resolved `anthill.reflect.TupleLiteral` entity symbol, cached
    /// so the typer's `is_tuple_lit` (run per constructor argument during inference)
    /// compares a `Symbol` instead of the 27-char `qualified_name_of(..) ==
    /// "anthill.reflect.TupleLiteral"` string per call. `None` until reflect is
    /// loaded (refreshed at [`crate::kb::typing::type_check_sorts_typed`] start,
    /// where every reflect fact is asserted); `is_tuple_lit` falls back to the exact
    /// string compare when unset, so behaviour is identical either way. The tuple
    /// constructor name the loader stamps is the same `by_qualified_name` canonical
    /// symbol this resolves to (load.rs), so the `Symbol ==` is exact.
    pub(crate) tuple_literal_sym: Option<Symbol>,

    /// WI-429: every `RigidTypeProjection` the loader FORMS, with its source
    /// span — the work-list for the end-of-load formation sweep
    /// (`typing::validate_rigid_projection_formations`). A projection stored
    /// in a position the typer never eliminates (an entity field type, a
    /// fact/rule type slot) would otherwise carry a malformed projection
    /// (typo'd member, bare-spec subject) silently. Drained by the sweep at
    /// the end of each load phase.
    pub(crate) rigid_projection_formations: Vec<(TermId, SourceSpan)>,

    /// WI-402 (existential half): the operations whose return type the loader
    /// REWROTE from an existential carrier (`-> C ensures Spec[C, …]` → the spec
    /// with the carrier dropped). The `abstracting_return` (WI-401) gate skips
    /// exactly these — an `ensures` admits the abstract return only when the loader
    /// actually formed the existential, NOT for any op that merely names the return
    /// sort in an `ensures` (that stays the strict escape). Keyed on the op symbol.
    pub(crate) existential_return_ops: std::collections::HashSet<Symbol>,

    /// WI-664 — entity-constructor functors whose SORT is classified `NonEq`: its
    /// congruent (field-wise) equality is non-reflexive because it reaches an
    /// unshielded partial `Float` leaf, NOT behind a lawful-Eq own-`eq` boundary
    /// (`TotalFloat`/`Set`/`Map`). The SEMANTIC `eq` of such a value is computed
    /// FIELD-WISE (`eq(Point(nan,_), Point(nan,_)) = eq(nan,nan) ∧ … = false`),
    /// agreeing with the field-wise C++ `operator==`, instead of taking the
    /// structural reflexivity shortcut (which would launder a nested NaN). Built
    /// once post-load by [`eq_derive::run`]; read by the resolver
    /// (`sem_eq_core`) and interpreter (`eval::builtins::semantic_equal`) via
    /// [`Self::value_reaches_partial_carrier`]. Empty ⇒ zero behavioral change
    /// (a KB with no Float-containing composites is byte-identical to pre-WI-664).
    pub(crate) field_wise_noneq_carriers: std::collections::HashSet<Symbol>,

    // WI-348 (value-fact payoff): the `op_effects` side-table is GONE. A
    // `denoted`-bearing effect label (`Modify[c]`) now lives in the
    // `OperationInfo` fact itself — the loader builds that fact as a *value
    // fact* (a `Value::Node` head carrying a value effects list) and
    // `lookup_operation_info` reads the effects back from the fact. This is
    // the side-table collapse the WI-348 design doc names as the payoff:
    // effects ride in the queryable fact, not a Rust-side map.

    // Entity field type registry: functor symbol → [(field_name, type_term)].
    // Populated during load_entity, used by type_check_sorts.
    entity_field_types: HashMap<Symbol, Vec<(Symbol, crate::eval::value::Value)>>,

    // WI-835 — every PARAMETERIZED TYPE INSTANTIATION the author WRITES: see
    // [`ParameterizedSite`] for what one is and which lowerings record them.
    //
    // RECORDED rather than checked in place because the check needs a COMPLETE
    // `provides` relation: `eq_derive::run` is the last load pass to assert
    // `SortProvidesInfo`, and a Float-composite key's `NonEq` comes from it, so
    // deciding at the lowering would silently pass every derived case.
    //
    // Push-only WITHIN a load; drained by the check (`take_parameterized_type_sites`)
    // so a second `load_incremental` into the same KB re-checks only ITS OWN sites.
    // Leaving them would re-walk and re-report every earlier batch's sites — the
    // reason the sibling `resolved_requires_facts` below exists.
    parameterized_type_sites: Vec<ParameterizedSite>,

    // SortRequiresInfo facts already finalized by resolve_requires_bindings.
    // Keyed by post-reassert RuleId. Lets incremental loads skip stdlib facts.
    resolved_requires_facts: HashSet<RuleId>,

    // Source registry (file names/paths)
    pub(crate) sources: SourceRegistry,

    // Extent-source registry (proposal 057, WI-796/WI-797) — per-functor read
    // owners, successor to the retired `RouteHandler`/`routes` registry. Sources
    // in a `SourceId`-keyed slab, a functor→owner mount table, and materialized
    // per-functor read profiles. Empty by default; populated via
    // `register_extent_owner`. The resolver consults a mount through
    // `SearchStream::gather_extent_rows` and the loader refuses a resident
    // collision (WI-797). See `kb/extent.rs`.
    pub(crate) extents: extent::ExtentRegistry,

    // WI-218 — static-dispatch rewrite tables.
    // `dispatch_rewrites`: original apply TermId → rewritten apply TermId
    //   (with `fn` substituted from spec op to impl op). The
    //   post-typing rewrite pass uses this to substitute apply terms
    //   bottom-up in operation bodies.
    // `dispatch_origin`: rewritten apply TermId → original spec op symbol.
    //   Read by reflection / proof-record specialization / debug tooling
    //   for provenance ("this was originally Spec.op, dispatched to
    //   Impl.op"). The interpreter never reads it.
    pub(crate) dispatch_rewrites: HashMap<TermId, TermId>,
    pub(crate) dispatch_origin: HashMap<TermId, Symbol>,

    // WI-226 Cache A — memoized FLATTENED direct `requires` chain per sort.
    // WI-657(12) revived this (WI-230 → WI-657 it was dormant): it now caches the
    // flattened `Rc<Vec<RequiresEntry>>` that `typing::direct_requires_chain_rc`
    // returns — the per-op `set_enclosing_sort` snapshot is then an `Rc` bump, not a
    // fresh Vec + per-entry clone off the (already-cached) `requires_tree`. Derived
    // purely from `requires_tree`, so it MUST be — and is — cleared together with
    // `requires_tree_cache` by `invalidate_requires_chain_cache` whenever
    // `SortRequiresInfo` changes; it can never outlive the tree it flattened. (Note:
    // the `requires_chain_cache_contains` accessor reads `requires_tree_cache`, not
    // this field.)
    pub(crate) requires_chain_cache: RefCell<HashMap<Symbol, Rc<Vec<crate::kb::typing::RequiresEntry>>>>,

    // WI-230 — memoized substitution-composed `requires` tree per sort.
    // Each entry is the `Rc<Vec<RequiresNode>>` `requires_tree(kb, S)`
    // returns. Same lifetime as Cache A: fills lazily during typing;
    // invalidated by `invalidate_requires_chain_cache`.
    pub(crate) requires_tree_cache: RefCell<HashMap<Symbol, Rc<Vec<crate::kb::typing::RequiresNode>>>>,

    // Memoized synthesized requirement-param names per parent sort —
    // `__req_<spec short name>` in chain order. Same lifetime as the
    // requires caches (derives from the chain); invalidated by
    // `invalidate_requires_chain_cache`. Avoids rebuilding the Vec +
    // collision-disambiguation HashMap on every frame push.
    pub(crate) synth_req_names_cache: RefCell<HashMap<Symbol, Rc<Vec<Symbol>>>>,

    /// WI-869 — memoized DICTIONARY chain per carrier: the sort's own `requires`
    /// chain followed by its conditional provisions' `:- goals` (`typing::
    /// provider_dict_chain`). Cleared by `invalidate_requires_chain_cache` alongside
    /// the two caches above, whose `requires_tree` it derives from — and, WI-1033, ALSO
    /// from `ProvidesConditionInfo` facts, which nothing retracts or re-asserts after
    /// the load that emits them.
    pub(crate) provider_dict_chain_cache:
        RefCell<HashMap<Symbol, Rc<crate::kb::typing::ProviderDictChain>>>,

    // WI-424 — memoized `(param symbol, canonical Var term)` pairs per
    // parametric sort (`typing::sort_type_params_as_pairs`). Consulted on hot
    // paths (per apply call site in the typer's receiver classification, per
    // value-directed dispatch at eval); the uncached computation walks the
    // whole symbol table + per-param SortAlias scans. A sort's params and
    // their alias facts are fixed at scan/load time, so entries never go
    // stale within a session.
    pub(crate) sort_param_pairs_cache: RefCell<HashMap<Symbol, Rc<Vec<(Symbol, TermId)>>>>,

    // WI-226 Cache B — memoized spec-op SLD dispatch results, keyed by
    // `(op_short, SortGoal, scope)`. Saves re-walking `SortProvidesInfo`
    // for repeated spec-op calls at the same (spec, bindings, scope) —
    // common in bodies that call `eq(a, b); eq(c, d); …` at the same T.
    //
    // The scope is captured as `Vec<RequiresEntry>` in the key, so calls
    // from different enclosing sorts don't collide. Within one body the
    // scope is fixed and the key effectively reduces to the goal + op.
    //
    // WI-507: the op's short-name symbol is part of the key. The cached
    // `DispatchOutcome` resolves the impl op via `sort_ops_lookup(impl_sort,
    // op_short)`, so two DIFFERENT carrier-only ops on the SAME carrier
    // (e.g. `clear(s)` and `insert(s, x)` on a `MutableStack`) produce the
    // same goal but must NOT share a memo entry — without `op_short` the
    // first-resolved op poisons the other (`clear` → `MutableStack.insert`).
    //
    // Same lifetime caveat as Cache A: callers asserting new
    // `SortProvidesInfo` post-typing must call
    // `invalidate_resolve_cache`.
    //
    // WI-829: the trailing `bool` records whether the resolution ran with a
    // call-site σ context (`dispatch_spec_op_cached`'s `disambig`). σ makes the
    // scope `FromScope` check σ-precise (a shallow-vs-deep compound frame entry
    // no longer coarse-covers a deeper goal), so the σ-present and σ-less regimes
    // can produce DIFFERENT outcomes for the same `(op, goal, scope)` and must
    // not share a memo entry. Within one regime the result is goal-determined
    // (body-local rigids appear in the goal), so caching stays sound.
    //
    // WI-841: the trailing `Vec<InstanceSelection>` is what the CALL SITE explicitly
    // selected (058 §4.5 step 0). Unlike the σ flag beside it, its CONTENT decides the
    // outcome — a pinned goal resolves to the pinned impl — so the list itself is the
    // key, not merely whether one was present.
    pub(crate) resolve_cache: RefCell<
        HashMap<
            (
                Symbol,
                crate::kb::typing::SortGoal,
                Vec<crate::kb::typing::RequiresEntry>,
                bool,
                Vec<crate::kb::typing::InstanceSelection>,
            ),
            (crate::kb::typing::DispatchOutcome, Option<crate::kb::typing::ResolvedRequiresNode>),
        >,
    >,

    // WI-240 — per-impl-sort operations table; see `SortOpsTable`.
    // Built at load time, read by dispatch consumers via
    // `sort_ops_lookup`.
    pub(crate) sort_ops: SortOpsTable,
    // WI-876 — operations a binding block gave a host implementation
    // (`operation_map`). The cache and the two membership indexes derived from it;
    // all three written by `load::build_host_op_mappings`. See `is_host_mapped_op`
    // and `is_interpreter_mapped_op` for why the indexes differ.
    host_mapped_ops: std::collections::HashSet<Symbol>,
    interpreter_mapped_ops: std::collections::HashSet<Symbol>,
    host_op_mappings: Vec<load::HostOperationMapping>,
    // WI-889 — bodyless `const`s a binding block gave a host value source
    // (`const_map`). Written by `load::build_host_const_mappings`. No membership
    // index alongside it, unlike `host_op_mappings`: a const is a value source read
    // by `force_const`, not a dispatch target the typer routes on.
    host_const_mappings: Vec<load::HostConstMapping>,
    // WI-860 (058 §3.6) — the materialized `default_provider` relation. Written by
    // `defaults::build_default_provider_index` once every `SortProvidesInfo` fact is
    // asserted. `None` on a KB that never ran that pass, which is NOT the same as an
    // empty index and is why this is an `Option`: a bare hand-built KB must not read as
    // "measured, and no carrier has a default". Nothing consumes it yet — 058 rung 2a
    // is WI-861.
    default_providers: Option<defaults::DefaultProviderIndex>,
}

/// WI-709: how a sort application's type arguments failed to fit the sort's declared
/// type params. Produced by [`KnowledgeBase::check_sort_type_args`] and rendered by
/// [`TypeArgProblem::describe`], so the type-position (`LoadError::InvalidTypeArgument`)
/// and value-position (`TypeError::InvalidTypeArgument`) diagnostics read the same.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeArgProblem {
    /// A named type argument keys a param the sort never declares — `Cell[W = Int64]`,
    /// where `Cell` declares only `V`.
    UndeclaredParam { param: String },
    /// More positional type arguments than there are declared params left to bind —
    /// `Cell[Int64, String]`, or any argument at all on a non-parametric sort.
    ExcessPositional { given: usize, free: usize },
    /// WI-764: one param bound TWICE — `Relation[T = A, T = B]`. A type application binds
    /// each param once; two bindings for one slot are two contradictory claims about the
    /// same type, and nothing downstream can pick between them. Caught at the gate that
    /// already validates a type application's named arguments, because every consumer that
    /// later reads bindings by param key resolves one of the two silently: `binding_for_param`
    /// takes the first, so `Relation[T = <right>, T = <wrong>]` checked clean while the
    /// reverse order rejected — a wrong schema accepted, order-dependently.
    ///
    /// Scoped to a `Sort` head, like the rest of this check: a non-Sort head (a type-param
    /// carrier `F` of a `sort Spec[F[T]]`, an entity head) returns early and is NOT covered,
    /// so this is a gate on the common path rather than a universal guarantee — consumers
    /// still must not depend on a bindings list being duplicate-free.
    DuplicateParam { param: String },
}

impl TypeArgProblem {
    /// One message, shared by both positions' diagnostics.
    pub fn describe(&self, kb: &KnowledgeBase, sort_sym: Symbol) -> String {
        let sort = kb.qualified_name_of(sort_sym);
        let declared = kb.type_params_of_sort(sort_sym);
        let declares = if declared.is_empty() {
            "declares no type parameters".to_owned()
        } else {
            format!("declares type parameter(s) {}", declared.join(", "))
        };
        match self {
            TypeArgProblem::UndeclaredParam { param } => {
                format!("`{sort}` has no type parameter named '{param}' — it {declares}")
            }
            TypeArgProblem::DuplicateParam { param } => format!(
                "`{sort}` binds the type parameter '{param}' more than once — a type \
                 application binds each parameter once, and two bindings for one slot are \
                 two contradictory claims about the same type"
            ),
            TypeArgProblem::ExcessPositional { given, free } => format!(
                "`{sort}` is over-applied: {given} positional type argument(s) but only \
                 {free} declared type parameter(s) left to bind — it {declares}"
            ),
        }
    }
}

impl KnowledgeBase {
    /// WI-628 — the carrier-`eq` sub-proof depth budget used in production
    /// ([`Self::prove_rule_predicate`]); a `cfg(test)` field overrides it in tests.
    pub(crate) const DEFAULT_SEM_EQ_SUB_DEPTH: usize = 100_000;

    pub fn new() -> Self {
        Self {
            terms: TermStore::new(),
            symbols: SymbolTable::new(),
            #[cfg(test)]
            sem_eq_sub_depth: Self::DEFAULT_SEM_EQ_SUB_DEPTH,
            rules: Vec::new(),
            rules_by_functor: HashMap::new(),
            bodied_rule_counts: HashMap::new(),
            rules_by_label: HashMap::new(),
            by_domain: HashMap::new(),
            sort_entities: HashMap::new(),
            entity_parent: HashMap::new(),
            sort_info: HashMap::new(),
            discrim: SubstTree::new(),
            fact_dedup: HashMap::new(),
            value_fact_dedup: HashMap::new(),
            synth_rule_memo: HashMap::new(),
            builtins: HashMap::new(),
            entity_fields: HashMap::new(),
            constructor_symbols: HashSet::new(),
            next_var: 0,
            sort_base_subst: HashMap::new(),
            sort_sort: None,
            entity_of_sort: None,
            guards: Vec::new(),
            guards_by_sort: HashMap::new(),
            term_spans: HashMap::new(),
            functor_spans: HashMap::new(),
            op_records: HashMap::new(),
            op_capture_params: HashMap::new(),
            named_requirement_slots: HashMap::new(),
            provider_dict_chain_cache: RefCell::new(HashMap::new()),
            sort_alias_index: None,
            provides_index: None,
            sort_info_index: None,
            const_types: HashMap::new(),
            const_bodies: HashMap::new(),
            has_dot_applies: false,
            simp_gate_cache: None,
            eq_connective_sym: None,
            unify_connective_sym: None,
            tuple_literal_sym: None,
            rigid_projection_formations: Vec::new(),
            existential_return_ops: std::collections::HashSet::new(),
            field_wise_noneq_carriers: std::collections::HashSet::new(),
            entity_field_types: HashMap::new(),
            parameterized_type_sites: Vec::new(),
            resolved_requires_facts: HashSet::new(),
            sources: SourceRegistry::new(),
            extents: extent::ExtentRegistry::new(),
            dispatch_rewrites: HashMap::new(),
            dispatch_origin: HashMap::new(),
            requires_chain_cache: RefCell::new(HashMap::new()),
            requires_tree_cache: RefCell::new(HashMap::new()),
            synth_req_names_cache: RefCell::new(HashMap::new()),
            sort_param_pairs_cache: RefCell::new(HashMap::new()),
            resolve_cache: RefCell::new(HashMap::new()),
            sort_ops: SortOpsTable::default(),
            host_mapped_ops: std::collections::HashSet::new(),
            interpreter_mapped_ops: std::collections::HashSet::new(),
            host_op_mappings: Vec::new(),
            host_const_mappings: Vec::new(),
            default_providers: None,
        }
    }

    /// Drop the memoized `requires_chain` results. Called when a new
    /// `SortRequiresInfo` fact is asserted after the cache filled, so
    /// stale chains can't be served. WI-226 / WI-230. Clears both the
    /// flat chain cache and the tree cache.
    #[allow(dead_code)]
    pub fn invalidate_requires_chain_cache(&self) {
        self.requires_chain_cache.borrow_mut().clear();
        self.requires_tree_cache.borrow_mut().clear();
        self.synth_req_names_cache.borrow_mut().clear();
        self.provider_dict_chain_cache.borrow_mut().clear();
    }

    /// Drop the memoized spec-op SLD dispatch results. Called when a
    /// new `SortProvidesInfo` fact is asserted after the cache filled.
    /// WI-226.
    #[allow(dead_code)]
    pub fn invalidate_resolve_cache(&self) {
        self.resolve_cache.borrow_mut().clear();
    }

    /// WI-226: number of entries in the resolve cache. Diagnostic /
    /// test inspector — counts how many `(goal, scope)` pairs have
    /// been memoized.
    pub fn resolve_cache_len(&self) -> usize {
        self.resolve_cache.borrow().len()
    }

    /// WI-226 / WI-230: does the `requires_chain` (tree) cache hold an
    /// entry for `sort_sym`? Diagnostic / test inspector —
    /// distinguishes pre-first-call (empty) from post-first-call
    /// (memoized) state. After WI-230 this points at the tree cache,
    /// which is the canonical source of `requires_chain` results.
    pub fn requires_chain_cache_contains(&self, sort_sym: Symbol) -> bool {
        self.requires_tree_cache.borrow().contains_key(&sort_sym)
    }

    /// Record that `original_apply` should be rewritten to `rewritten_apply`
    /// (a new apply term with `fn` substituted from spec op to impl op),
    /// and remember `spec_op_sym` as the original spec call's symbol.
    /// WI-218: typing-time spec→impl rewrite for static dispatch.
    /// Exposed publicly so tests and out-of-tree elaboration passes can
    /// stage their own term-level rewrites alongside the typer's.
    pub fn record_dispatch_rewrite(
        &mut self,
        original_apply: TermId,
        rewritten_apply: TermId,
        spec_op_sym: Symbol,
    ) {
        self.dispatch_rewrites.insert(original_apply, rewritten_apply);
        self.dispatch_origin.insert(rewritten_apply, spec_op_sym);
    }

    /// True iff `term` was rewritten from a spec-op call. Returns the
    /// original spec op symbol for provenance / debug / reflection.
    /// The interpreter does not consult this — runtime semantics use
    /// the rewritten term's `fn` directly.
    pub fn dispatch_origin_of(&self, term: TermId) -> Option<Symbol> {
        self.dispatch_origin.get(&term).copied()
    }

    /// Iterate (rewritten_term, original_spec_op) pairs. Useful for
    /// reflection, debug tooling, and tests.
    pub fn dispatch_origin_iter(&self) -> impl Iterator<Item = (TermId, Symbol)> + '_ {
        self.dispatch_origin.iter().map(|(t, s)| (*t, *s))
    }

    /// Look up the rewritten TermId an original term maps to, if any.
    /// Reflection / tooling / external-elaboration consumers read this
    /// to see what an apply (or any term) was rewritten to.
    pub fn dispatch_rewrite_of(&self, original: TermId) -> Option<TermId> {
        self.dispatch_rewrites.get(&original).copied()
    }

    /// Register a synthesizing pass by qualified name. Returns a PassId
    /// that can be passed to `the legacy alloc_synthesized helper`'s `by:`
    /// field. Idempotent — re-registering returns the same PassId.
    /// Passes call this at startup (or first use) to obtain their identifier.
    pub fn register_pass(&mut self, qualified_name: &str) -> crate::kb::occurrence::PassId {
        crate::kb::occurrence::PassId::from_symbol(self.symbols.intern(qualified_name))
    }

    /// Has this SortRequiresInfo fact already been finalized
    /// (operations auto-bound) by resolve_requires_bindings?
    pub fn is_requires_resolved(&self, rid: RuleId) -> bool {
        self.resolved_requires_facts.contains(&rid)
    }

    /// Mark a (post-reassert) SortRequiresInfo RuleId as finalized.
    pub fn mark_requires_resolved(&mut self, rid: RuleId) {
        self.resolved_requires_facts.insert(rid);
    }

    // ── Source & occurrence access ─────────────────────────────

    pub fn register_source(&mut self, name: String) -> crate::span::SourceId {
        self.sources.register(name)
    }

    pub fn source_name(&self, id: crate::span::SourceId) -> &str {
        self.sources.name(id)
    }

    /// WI-242 — get the value-typed body node for an operation, if the
    /// loader produced one. None for body-less ops (spec declarations).
    pub fn op_body_node(&self, op_sym: Symbol) -> Option<&Rc<NodeOccurrence>> {
        self.op_records.get(&op_sym).and_then(|r| r.body.as_ref())
    }

    /// WI-727 (proposal 056) — the name of `op_sym`'s VARIADIC CAPTURE parameter
    /// (`...args: R`), if it declares one. `None` for the vast majority of ops. Read
    /// by the typer's argument matching to route leftover named arguments into the
    /// capture record. Recorded by the loader ([`Self::record_op_capture_param`]).
    pub fn op_capture_param(&self, op_sym: Symbol) -> Option<Symbol> {
        self.op_capture_params.get(&op_sym).copied()
    }

    /// WI-727 — record `op_sym`'s variadic capture parameter name. Called by the
    /// loader when an operation declares a `...`-marked parameter.
    pub fn record_op_capture_param(&mut self, op_sym: Symbol, param: Symbol) {
        self.op_capture_params.insert(op_sym, param);
    }

    /// WI-840 (058 §4.7) — record that `owner`'s requirement slot at position `slot`
    /// is NAMED `binder` and demands the spec based at `spec_base`. Called by the
    /// loader for both spellings of the named form: a sort's `requires O: Ord[T]` and
    /// an operation's `requires plus: Monoid[T]`. Appended in source order, so
    /// `named_requirement_slots(owner)` reads back the declaration order.
    pub fn record_named_requirement_slot(
        &mut self,
        owner: Symbol,
        binder: Symbol,
        slot: usize,
        spec_base: Option<Symbol>,
    ) {
        self.named_requirement_slots
            .entry(owner)
            .or_default()
            .push(NamedRequirementSlot { binder, slot, spec_base });
    }

    /// WI-840 — `owner`'s NAMED requirement slots in declaration order; empty for the
    /// overwhelmingly common all-anonymous owner.
    pub fn named_requirement_slots(&self, owner: Symbol) -> &[NamedRequirementSlot] {
        self.named_requirement_slots.get(&owner).map_or(&[], Vec::as_slice)
    }

    /// WI-242 — record the value-typed body node for an operation.
    /// Called by the loader during operation conversion, and by the typer's
    /// `[simp]`-rewrite write-back. WI-656: writes `record.body` in place, so the
    /// cached signature beside it is undisturbed.
    pub fn set_op_body_node(&mut self, op_sym: Symbol, node: Rc<NodeOccurrence>) {
        self.op_records.entry(op_sym).or_default().body = Some(node);
    }

    /// WI-656 — the unified per-operation record (cached signature + body node),
    /// if this operation has one. Backs `op_info::lookup_operation_info`'s O(1)
    /// fast path.
    pub(crate) fn op_record(&self, op_sym: Symbol) -> Option<&op_info::OperationRecord> {
        self.op_records.get(&op_sym)
    }

    /// Proposal 039 / WI-084 — the declared type of a term-level constant, if
    /// `const_sym` names one. `None` for any non-const symbol.
    pub fn const_type(&self, const_sym: Symbol) -> Option<&crate::eval::value::Value> {
        self.const_types.get(&const_sym)
    }

    /// Proposal 039 / WI-084 — record a constant's declared type (loader).
    pub fn set_const_type(&mut self, const_sym: Symbol, ty: crate::eval::value::Value) {
        self.const_types.insert(const_sym, ty);
    }

    /// Proposal 039 / WI-084 — the defining-expression body of a term-level
    /// constant, if one was stored. `None` for a bodyless (host-supplied) const.
    pub fn const_body_node(&self, const_sym: Symbol) -> Option<&Rc<NodeOccurrence>> {
        self.const_bodies.get(&const_sym)
    }

    /// Proposal 039 / WI-084 — record a constant's body node (loader).
    pub fn set_const_body_node(&mut self, const_sym: Symbol, node: Rc<NodeOccurrence>) {
        self.const_bodies.insert(const_sym, node);
    }

    /// WI-251 — span for a stored term, if the loader recorded one.
    pub fn term_span(&self, t: TermId) -> Option<crate::span::SourceSpan> {
        self.term_spans.get(&t).copied()
    }

    /// WI-251 — first span recorded for `functor` during load, if any.
    pub fn functor_span(&self, functor: Symbol) -> Option<crate::span::SourceSpan> {
        self.functor_spans.get(&functor).copied()
    }

    /// WI-458 — this rule/fact head's OWN source span, if the loader recorded
    /// one. Unlike [`Self::term_span`] it is keyed by `RuleId`, so a head whose
    /// `TermId` is hash-cons-shared with another rule's head still resolves to
    /// THIS rule's source location. The head-error paths in typing.rs read this.
    pub fn rule_head_span(&self, id: RuleId) -> Option<crate::span::SourceSpan> {
        self.rules[id.index()].head_span
    }

    /// WI-458 — record a fact/rule head's own source span. First-write-wins: an
    /// `assert_fact` dedup hit hands back an EXISTING RuleId, and the surviving
    /// entry keeps its original (first-loaded) span — the one `RuleEntry` the
    /// duplicates collapsed onto.
    pub fn set_rule_head_span(&mut self, id: RuleId, span: crate::span::SourceSpan) {
        self.rules[id.index()].head_span.get_or_insert(span);
    }

    /// WI-251 — iterate every operation's `(symbol, body NodeOccurrence)`.
    /// Passes (e.g. `req_insertion::run`) that need to scan all bodies
    /// consume this; the iteration order is unspecified.
    pub fn op_bodies_iter(&self) -> impl Iterator<Item = (Symbol, &Rc<NodeOccurrence>)> + '_ {
        // WI-656 — records with no body (body-less spec ops) are skipped, so this
        // yields exactly the former `op_bodies` entries.
        self.op_records
            .iter()
            .filter_map(|(s, r)| r.body.as_ref().map(|b| (*s, b)))
    }

    /// Proposal 039 / WI-084 — iterate every anthill-bodied constant's
    /// `(symbol, body NodeOccurrence)`. The load-time purity gate consumes this
    /// to reject an effectful const body. Bodyless (host-supplied) consts have
    /// no entry. Iteration order is unspecified.
    pub fn const_bodies_iter(&self) -> impl Iterator<Item = (Symbol, &Rc<NodeOccurrence>)> + '_ {
        self.const_bodies.iter().map(|(s, n)| (*s, n))
    }

    /// Proposal 039 / WI-084 — iterate every constant's `(symbol, declared type
    /// Value)`. Unlike [`Self::const_bodies_iter`], this covers EVERY const
    /// (every const has a declared type), bodied or bodyless. Codegen (WI-533)
    /// consumes this to discover the consts in a sort/namespace scope — consts
    /// emit no scope-member fact, so they are absent from the fact index and
    /// must be found by scanning. Iteration order is unspecified.
    pub fn const_types_iter(&self) -> impl Iterator<Item = (Symbol, &crate::eval::value::Value)> + '_ {
        self.const_types.iter().map(|(s, v)| (*s, v))
    }

    // ── Term allocation ─────────────────────────────────────────

    /// The `TermId` of an already-interned term, without interning or refcounting it
    /// (WI-849 review). For a caller that only needs to NAME a term it already holds
    /// alive through something else; [`Self::alloc`] would inflate the refcount on every
    /// such read. Deliberately does NOT reproduce `alloc`'s WI-511 nullary-`Fn` → `Ref`
    /// canonicalization, so pass the storage form you expect to find.
    pub fn find_term(&self, term: &Term) -> Option<TermId> {
        self.terms.find(term)
    }

    /// Allocate a term (hash-consed, refcounted).
    pub fn alloc(&mut self, term: Term) -> TermId {
        // WI-511: a nullary application of a registered constructor is stored in
        // its bare `Ref` form, so a fact written as `Fn{c}` and a rule pattern
        // spelled `Ref(c)` share ONE TermId. This ELIMINATES the dual
        // representation that WI-436 only bridged at the view layer
        // (`functor_view_head`): with a single storage form, raw `Term::Fn`
        // readers and `head()`-routed readers agree without a canonicalizer.
        // Gated on `is_constructor_symbol` (kind-isolated, same as the bridge):
        // ops-as-values are `Value::OpRef`, never `Term::Ref`, and sorts/params
        // aren't constructors, so the WI-391 `Ref`=wildcard / `Fn`=concrete
        // TYPE-dispatch distinction is untouched.
        if let Term::Fn { functor, pos_args, named_args } = &term {
            if pos_args.is_empty() && named_args.is_empty() && self.is_constructor_symbol(*functor) {
                let f = *functor;
                return self.terms.alloc(Term::Ref(f));
            }
        }
        self.terms.alloc(term)
    }

    /// Intern a string, returning a Symbol.
    pub fn intern(&mut self, s: &str) -> Symbol {
        self.symbols.intern(s)
    }

    /// Mint a FRESH, distinct Unresolved symbol displaying as `name` (WI-550) —
    /// the alpha-rename of a local binder to a per-binding-site identity. See
    /// [`crate::intern::SymbolTable::intern_unique`].
    pub fn intern_unique(&mut self, name: &str) -> Symbol {
        self.symbols.intern_unique(name)
    }

    /// Define a Resolved symbol in the given scope. Wrapper exposing
    /// `SymbolTable::define` for downstream crates that need to
    /// register synthesized symbols (e.g. anthill-cli's
    /// `dispatch_structured` synthesizing transient step rules).
    /// Idempotent on re-definition: returns the existing symbol if
    /// `short_name` already lives in the scope.
    pub fn define_symbol(
        &mut self,
        short_name: &str,
        qualified_name: &str,
        kind: crate::intern::SymbolKind,
        scope: ScopeId,
    ) -> Symbol {
        self.symbols.define(short_name, qualified_name, kind, scope)
    }

    /// Allocate a fresh logic variable id, carrying the display name.
    pub fn fresh_var(&mut self, name: Symbol) -> VarId {
        let id = self.next_var;
        self.next_var += 1;
        VarId::new(id, name)
    }

    /// `sym`'s name WITHIN THE SCOPE THAT DECLARES IT — the key it is filed under in
    /// that scope. `fill` for `Tank.fill`. Pairs with [`Self::qualified_name_of`],
    /// which answers the other half of the same question.
    ///
    /// LOCAL, not SHORT, and the difference is real: it is usually one segment but
    /// need not be. A WI-341 callback place is declared in the OPERATION's scope under
    /// its path relative to that operation, so `anthill.prelude.Monad.flatMap.f._1`
    /// answers `f._1` — the dot keeps it distinct from a sibling callback's `_1` in
    /// the one flat scope map. MEASURED over stdlib + anthill-stl: 53 of 2598 symbols
    /// answer with a dotted name, all of that shape.
    ///
    /// So this is NOT `typing::short_name_of`, which slices the last segment off a
    /// qualified name STRING, nor the language-level `anthill.reflect.short_name`,
    /// which `rsplit`s for the same reason. Those two answer `_1`; this answers
    /// `f._1`. Composing them (`short_name_of(kb.local_name_of(sym))`) is a real and
    /// common idiom — the two are not interchangeable.
    ///
    /// Named `resolve_sym` until WI-956. That read as a sibling of
    /// [`Self::resolve_symbol`] / [`Self::try_resolve_symbol`] — one truncation apart
    /// from it — while running in the OPPOSITE direction: those take a name and answer
    /// a `Symbol`, this takes a `Symbol` and answers a name.
    pub fn local_name_of(&self, sym: Symbol) -> &str {
        self.symbols.local_name(sym)
    }

    /// Get the qualified name for a resolved Symbol.
    /// Returns the short name if the symbol is unresolved.
    pub fn qualified_name_of(&self, sym: Symbol) -> &str {
        match self.symbols.get(sym) {
            SymbolDef::Resolved { qualified_name, .. } => qualified_name,
            SymbolDef::Unresolved { name } => name,
        }
    }

    /// The qualified names behind a [`ResolveResult::Ambiguous`], for a diagnostic that
    /// names what it could not choose between.
    pub fn candidate_names(&self, candidates: &[Symbol]) -> Vec<String> {
        candidates.iter().map(|&sym| self.qualified_name_of(sym).to_string()).collect()
    }

    /// The keyword `sym`'s declaration opened with — for DISPLAY (a diagnostic,
    /// reflect's `kind` string). `None` for unresolved symbols.
    ///
    /// NOT a test for what the name may be used as. One name can play several
    /// roles (§6.3: an eponymous constructor IS its sort, so `Project` is both a
    /// `Sort` and an `Entity`), and this reports only the first-declared one — so
    /// `kind_of(s) == Some(Sort)` answers "was it written with `sort`", which for
    /// the two spellings of one §6.3 declaration gives two different answers. Ask
    /// [`Self::has_kind`] instead whenever the question is "can this name serve as
    /// an X".
    pub fn kind_of(&self, sym: Symbol) -> Option<crate::intern::SymbolKind> {
        self.symbols.get(sym).primary_kind()
    }

    /// Does `sym` play role `kind`? The membership question — insensitive to
    /// which keyword came first, and therefore to source order.
    pub fn has_kind(&self, sym: Symbol, kind: crate::intern::SymbolKind) -> bool {
        self.symbols.get(sym).has_kind(kind)
    }

    /// The symbol that owns the lexical scope in which `sym` was declared
    /// (`Tank` for `Tank.fill`). `None` only for an UNRESOLVED symbol, which has
    /// no scope at all.
    ///
    /// WI-984 — the `None` used to have a second cause, and it was the common one.
    /// See [`ScopeId`] for the mechanism and the measurement.
    pub fn declaring_scope_symbol(&self, sym: Symbol) -> Option<Symbol> {
        self.symbols.declaring_scope(sym).map(|s| s.owner())
    }

    /// WI-984 — the TOP-LEVEL scope, `_global`. One spelling: the incantation was
    /// otherwise written 19 times across five files in two forms (a
    /// `make_name_term("_global")` round trip through the term store, and a bare
    /// `intern` + mint), under four different local names.
    pub fn global_scope(&mut self) -> ScopeId {
        let sym = self.symbols.intern("_global");
        self.symbols.scope_id(sym)
    }

    /// Type-parameter names declared inside a sort's body (`sort T = ?`
    /// inside `sort S { ... }`). Returns the names in alphabetical
    /// order — stable across runs but not necessarily source order.
    /// Empty when the sort has no body, no children, or no params.
    pub fn type_params_of_sort(&self, sort_sym: Symbol) -> Vec<String> {
        let qn = self.qualified_name_of(sort_sym);
        let prefix = format!("{qn}.");
        // Find the body scope by looking only at *direct* children of
        // the sort — qualified names with no further dots after the
        // prefix. `HashMap.iter()` order is non-deterministic, so a
        // grandchild (e.g. an operation parameter) would otherwise
        // sometimes win and yield the wrong scope.
        let body_scope = self.symbols.by_qualified_name.iter()
            .find_map(|(child_qn, child_sym)| {
                if !child_qn.starts_with(&prefix) { return None; }
                if child_qn[prefix.len()..].contains('.') { return None; }
                self.symbols.declaring_scope(*child_sym)
            });
        let Some(body_scope) = body_scope else { return Vec::new() };
        let Some(scope) = self.symbols.scope(body_scope) else { return Vec::new() };
        // Source-order, not alphabetical: positional sort bindings rely
        // on declaration order (`Map[String, Int]` mapping index 0→K,
        // 1→V follows the order K and V were declared, not their
        // alphabetic sort). The HashSet path is still used by
        // `is_type_param` membership checks.
        scope.type_params_ordered.clone()
    }

    /// WI-709: check a sort APPLICATION's type arguments against the sort's DECLARED
    /// type params — the ONE rule both positions a type can be written in must obey.
    ///
    /// A type in TYPE position (`c: Cell[W = Int64]`) and the same type in VALUE
    /// position (`is_modifiable(Cell[W = Int64])`, WI-707) lower through the SAME
    /// canonical builder ([`Self::make_parameterized_type`]) so they hash-cons to one
    /// term; that identity only holds if the two positions also AGREE on which
    /// arguments are admissible. Without this check they did not: the written form
    /// carried a stray `W` binding, an over-applied positional was silently dropped at
    /// load, and eval rejected the same positional at run time — three answers to one
    /// written type. Both callers (the loader's `type_expr_to_child`, the typer's
    /// sort-application arm) run this check, so eval's own guard
    /// (`Interpreter::finish_sort_type`) is a backstop for programmatically-built
    /// calls rather than the only place a typo is heard.
    ///
    /// Loud, per CLAUDE.md's loud-over-silent rule: an undeclared param name is a typo
    /// the author wants to hear about, and dropping it builds a type that silently
    /// means something else.
    ///
    /// `declared` is [`Self::type_params_of_sort`] for the head — passed in, not re-read,
    /// because that call scans the symbol table (both callers already hold the list, and
    /// a type annotation is a hot load path — WI-653). `named` are the argument keys AS
    /// WRITTEN (short names); `positional_count` the number of positional arguments, each
    /// of which binds the next declared param not already given by name (`Cell[Int64]` ≡
    /// `Cell[V = Int64]`).
    ///
    /// Skipped for a non-`Sort` head (an unresolved name — which already has its own
    /// diagnostic, so piling on would double-report — or an entity / value head, whose
    /// arguments are not sort type-args at all). This keeps the gate identical to the
    /// value-position arm's own `kind_of(..) == Sort` firing condition.
    pub fn check_sort_type_args(
        &self,
        sort_sym: Symbol,
        declared: &[String],
        named: &[Symbol],
        positional_count: usize,
    ) -> Result<(), TypeArgProblem> {
        if self.kind_of(sort_sym) != Some(crate::intern::SymbolKind::Sort) {
            return Ok(());
        }
        for (i, n) in named.iter().enumerate() {
            let short = self.local_name_of(*n);
            if !declared.iter().any(|d| d == short) {
                return Err(TypeArgProblem::UndeclaredParam { param: short.to_owned() });
            }
            // WI-764: reject a param bound twice. Compared by the SHORT name the argument
            // was written with (the same key `declared` is matched on just above), so the
            // two spellings one slot can arrive under never read as two distinct params.
            if named[..i].iter().any(|p| self.local_name_of(*p) == short) {
                return Err(TypeArgProblem::DuplicateParam { param: short.to_owned() });
            }
        }
        // Each positional binds the next declared param NOT already given by name, so
        // the params still free is what bounds the positional count — the same rule
        // `finish_sort_type` and the loader bind by.
        let free = declared
            .iter()
            .filter(|d| !named.iter().any(|n| self.local_name_of(*n) == d.as_str()))
            .count();
        if positional_count > free {
            return Err(TypeArgProblem::ExcessPositional { given: positional_count, free });
        }
        Ok(())
    }

    /// Get the Term for a TermId.
    pub fn get_term(&self, id: TermId) -> &Term {
        self.terms.get(id)
    }

    // ── Rule assertion / retraction ─────────────────────────────

    /// Assert a rule into the KB. The primary method: head + body + metadata.
    /// Facts are rules with an empty body. Uses `insert_pattern` to handle
    /// variables in the head. The term body is materialized to the rule's
    /// occurrence body — the sole stored form — via [`Self::term_body_to_nodes`].
    /// Rules whose vars must close to De Bruijn go through
    /// [`Self::assert_rule_debruijn_with_nodes`] (synthesized / hand-built) or
    /// the loader's native occurrence build; this entry asserts the head + body
    /// as given (ground facts, or callers that closed vars themselves).
    pub fn assert_rule(
        &mut self,
        head: TermId,
        body: Vec<TermId>,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        let body_nodes = self.term_body_to_nodes(&body);
        self.assert_rule_nodes(head, body_nodes, clause_kind, domain, meta)
    }

    /// Materialize a term body into the rule's occurrence body (WI-246/WI-372) —
    /// the single `Vec<TermId>` → `Vec<NodeOccurrence>` converter for every
    /// caller that builds a rule from terms (the primary [`Self::assert_rule`]
    /// and the synthesized / hand-built rules routed through
    /// [`Self::assert_rule_debruijn_with_nodes`]). Each atom is a read-only
    /// `materialize_from_handle` walk (De Bruijn / Global leaves preserved as
    /// `Expr::Var`); the term body is neither stored nor incref'd (its `RuleEntry`
    /// field was dropped). The loader builds occurrences natively from the parse
    /// IR and never comes through here. Empty body ⇒ empty occurrence body (a
    /// fact). The occurrence body is the resolver's goal source and the
    /// typer/`simp` view.
    pub fn term_body_to_nodes(&self, body: &[TermId]) -> Vec<Rc<NodeOccurrence>> {
        body.iter()
            .map(|&b| node_occurrence::materialize_from_handle(self, b))
            .collect()
    }

    /// Core rule-insertion epilogue: the occurrence body is already final (in the
    /// rule's stored form). Increfs head/sort/domain/meta, pushes the `RuleEntry`,
    /// and updates the sort / domain / functor / fact-dedup / discrimination
    /// indexes. The single storage path: callers materialize a term body to
    /// occurrences first ([`Self::term_body_to_nodes`]) or supply the loader's
    /// native occurrences, then close to De Bruijn via
    /// [`Self::finalize_rule_debruijn_nodes`] before landing here. Sets
    /// `arity`/`shared_arity`/`globals` to their ground-fact defaults; De Bruijn
    /// callers overwrite them.
    pub fn assert_rule_nodes(
        &mut self,
        head: impl Into<crate::eval::value::Value>,
        body_nodes: Vec<Rc<NodeOccurrence>>,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        // WI-373: the head is carrier-agnostic — a `Value::Term` for the
        // universal hash-consed case, or a `Value::Node`/`Entity` for a value
        // rule head carrying a denoted occurrence. Every existing caller passes a
        // `TermId` (→ `Value::Term` via `From`), so the term path is unchanged.
        // Builtins always take precedence over rules at resolution time (checked
        // first in step_init), so rules with builtin functors are allowed but
        // effectively shadowed during resolution.
        let head: crate::eval::value::Value = head.into();
        let is_fact = body_nodes.is_empty();
        // The hash-consed head term for the ground-fact dedup index below — only a
        // `Value::Term` head has one; a `Node`/`Entity` head is keyless (a dedup-miss,
        // not unsoundness — WI-348 Phase B). Read before `head` moves into the entry.
        let head_term = match &head {
            crate::eval::value::Value::Term { id: t, .. } => Some(*t),
            _ => None,
        };
        let rule_id = self.push_value_head_entry(head, body_nodes, clause_kind, domain, meta);

        // WI-233: ground-fact dedup index. Inserted only for body-empty entries
        // (rules with a body match structurally via the discrim tree, not
        // exact-equality) AND only for a `Term`-carrier head. We do not overwrite an
        // existing entry; the dedup check in `assert_fact` upstream routes duplicates
        // to the existing RuleId first.
        //
        // WI-472/WI-815: a `Node`/`Entity` value head is deduped instead by
        // [`Self::assert_fact_value`] (via a derived `GoalKey` in `value_fact_dedup`),
        // which is the sole entry point every value-fact producer uses
        // (`assert_fact_carrier` routes value heads there; value RULES have non-empty
        // bodies so `is_fact` is false here). A value head reaching THIS path with an
        // empty body has no current caller; it would be a benign dedup-MISS (stored,
        // just not collapsed) — never unsound — and retract stays symmetric because
        // it re-derives the value key from the head and finds no entry to remove.
        if is_fact {
            if let Some(t) = head_term {
                self.fact_dedup.entry((t, clause_kind, domain)).or_insert(rule_id);
            }
        }
        rule_id
    }

    /// Store a value head + occurrence body as a `RuleEntry` and index it
    /// carrier-agnostically (WI-348/WI-373) — the shared storage epilogue of
    /// [`Self::assert_rule_nodes`] and [`Self::assert_fact_value`], so the two
    /// cannot drift in how a value head is owned and indexed. Increfs the head's
    /// ground `TermId` leaves (a `Value::Term(t)` yields exactly `[t]`, matching
    /// the old `terms.incref(head)`; a `Node`/`Entity` head increfs its ground
    /// children — symmetric with `retract`'s `release_value_ground`) + meta
    /// (clause kind and domain are `Symbol`s — nothing to refcount), pushes the
    /// entry (arity/shared_arity/globals at
    /// ground-fact defaults — De Bruijn callers overwrite), indexes
    /// `by_clause_kind`/`by_domain`/`rules_by_functor` (functor via the head's
    /// `TermView`, any carrier), and inserts the head into the discrim tree
    /// through its `TermView`. Does NOT touch `fact_dedup` — that key is
    /// `Term`-only and caller-specific.
    fn push_value_head_entry(
        &mut self,
        head: crate::eval::value::Value,
        body_nodes: Vec<Rc<NodeOccurrence>>,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        let rule_id = RuleId(self.rules.len() as u32);

        // WI-635: collect the stored head's `Var::Global`s ONCE here (assert is
        // cold; the resolver reads the cached list, never re-walking the head). A
        // De Bruijn caller passes an already-closed head (no Globals → empty); a
        // ground fact has no head vars (→ empty); a non-ground arity-0 fact (the
        // loader's omitted-field fills, or a value fact carrying Globals) gets a
        // non-empty list, routing it off the raw-bind fast-path.
        let mut head_vars = Vec::new();
        let mut head_seen = std::collections::HashSet::new();
        self.collect_head_global_vars(&head, &mut head_vars, &mut head_seen);

        self.incref_value_ground(&head);
        if let Some(m) = meta {
            self.terms.incref(m);
        }

        // Top-level functor via the head's `TermView` (any carrier — WI-348).
        // WI-436: a 0-ary constructor head reads as the bare `Ref(c)`; `functor_sym`
        // reads `c` off either spelling so a nullary-constructor fact (`fact none`)
        // is still indexed under its functor symbol, mirroring the discrim tree
        // (which indexes it as `Ref(c)`).
        let head_functor = term_view::TermView::head(&head, self).functor_sym();

        // WI-581 guardrail. Both rule-firing indexes fed below key on this raw
        // head functor symbol with NO by-QN canonicalization: `rules_by_functor`
        // (the enumeration index, fed below) and the discrimination tree
        // (the SLD *resolution* index, queried via `query_view`). The query goal
        // flows from the same producers as the head, so the two sides match only
        // because they carry the *same* symbol. A WI-502 typed-rule / typed-value
        // producer that rekeys or synthesizes a head under a *same-FQN copy* — a
        // scan-time twin interned under a different `u32` for the same qualified
        // name — would index under a divergent symbol and SILENTLY no-match (no
        // fallback). `canonical_sym` bridges exactly those same-FQN copies, so
        // this fires the moment a producer drifts off the canonical symbol.
        //
        // It deliberately does NOT fire on a legitimately *undeclared* predicate
        // (`fact file_extension(...)`, datalog-style ad-hoc test facts, the
        // generated `_synth_N` memo rules): those are bare short-name interns
        // with no `by_qualified_name` entry, so `canonical_sym` returns the
        // identity and they pass. They are sound without being canonical — head
        // and goal bare-intern the same string to the same symbol (`intern_map`
        // dedup), so they agree. Per the CAVEAT on `canonical_sym`, a bare intern
        // is NOT bridged by-QN, so a *bare-head / FQN-goal* asymmetry cannot be
        // distinguished from a benign ad-hoc head at this choke point and is not
        // caught here — the realistic same-FQN-copy drift is.
        if let Some(f) = head_functor {
            debug_assert_eq!(
                self.canonical_sym(f),
                f,
                "WI-581: head functor {:?} ({:?}) is a non-canonical same-FQN \
                 copy of resolved symbol {:?}; resolve it to the canonical symbol \
                 at the producer before the head is stored (a divergent functor \
                 silently no-matches in both rule-firing indexes)",
                f,
                self.qualified_name_of(f),
                self.canonical_sym(f),
            );
        }

        // WI-812: capture fact-ness before `body_nodes` is moved into the entry,
        // to bump the `has_bodied_rule` gate below (a bodied rule = non-empty body).
        let is_bodied = !body_nodes.is_empty();

        self.rules.push(RuleEntry {
            head: head.clone(),
            body_nodes,
            clause_kind,
            domain,
            meta,
            retracted: false,
            arity: 0,
            globals: Vec::new(),
            shared_arity: 0,
            label: None,
            type_bounds: Vec::new(),
            head_vars,
            // WI-458: filled by the loader via `set_rule_head_span` once it has
            // this rule's RuleId; a synthesized head keeps `None`.
            head_span: None,
            // WI-472: set by `assert_fact_value` after this push, for a deduped
            // Node/Entity fact head. Every other head (rule, un-deduped, or a
            // `Value::Term` fact whose key is the head itself) leaves it `None`.
        });

        self.by_domain.entry(domain).or_default().push(rule_id);
        if let Some(f) = head_functor {
            self.rules_by_functor.entry(f).or_default().push(rule_id);
            // WI-812: one more indexed bodied rule under `f` — bump the O(1)
            // `has_bodied_rule` gate. Paired with the `retract` / `unindex_functor`
            // decrements; a fact leaves the gate untouched.
            if is_bodied {
                self.inc_bodied_rule_count(f);
            }
            // WI-665: recompute the simp gate lazily only when this head is an
            // `eq`/`unify` equation (superseding WI-646's drop-on-any-assert). A
            // head with no functor cannot be one, so skipping the drop there is
            // sound too. See `invalidate_simp_gate_if_connective`.
            self.invalidate_simp_gate_if_connective(f);
        }

        // Discrimination tree index (insert_pattern handles vars in head). The
        // view-driven walk needs `&self` (Node-carrying value heads read the
        // whole KB — WI-348), so run it with the index detached.
        self.with_discrim_detached(move |kb, discrim| {
            discrim.insert_pattern(kb, &head, rule_id);
        });

        rule_id
    }

    /// Run `f` with the discrimination index moved out of `self`, so a
    /// view-driven walk can read the whole KB (`&self` — Node-carrying value
    /// heads need it, WI-348) without aliasing `&mut self.discrim`. The index
    /// is always swapped back before returning — including when `f`
    /// early-returns — so the KB can never be left holding the empty
    /// placeholder (Phase A review guard #4). A panic inside `f` unwinds past
    /// the restore, but that already aborts the operation loudly.
    fn with_discrim_detached<R>(
        &mut self,
        f: impl FnOnce(&Self, &mut SubstTree<RuleId>) -> R,
    ) -> R {
        // Restore the index on drop — including on unwind — so a panic inside
        // `f` (the discrim ViewHead guards, the insert/remove `expect`s) can
        // never leave the KB holding the empty placeholder (WI-348 review #5).
        struct Restore<'a> {
            kb: &'a mut KnowledgeBase,
            discrim: SubstTree<RuleId>,
        }
        impl Drop for Restore<'_> {
            fn drop(&mut self) {
                self.kb.discrim = std::mem::replace(&mut self.discrim, SubstTree::new());
            }
        }
        let detached = std::mem::replace(&mut self.discrim, SubstTree::new());
        let mut guard = Restore { kb: self, discrim: detached };
        f(&*guard.kb, &mut guard.discrim)
    }

    // ── Guards ───────────────────────────────────────────────────

    /// Register a guard on the KB (WI-023). The guard is any [`TermView`] — a
    /// hash-consed `TermId` `LogicalQuery` (the loader's form today), a `Value`,
    /// or a `Value::Node` occurrence — stored carrier-agnostically and read back
    /// only through `TermView`, so the engine never assumes a `TermId`. Trigger
    /// sorts are auto-extracted from the structure.
    ///
    /// [`TermView`]: term_view::TermView
    pub fn add_guard<V: term_view::TermView>(&mut self, guard: V) -> ConstraintId {
        self.add_guard_labeled(guard, None)
    }

    /// [`add_guard`](Self::add_guard) carrying the source constraint's label for
    /// violation diagnostics.
    pub fn add_guard_labeled<V: term_view::TermView>(
        &mut self,
        guard: V,
        label: Option<String>,
    ) -> ConstraintId {
        use crate::eval::value::Value;
        use crate::kb::persist_subst::BindValue;
        // Own the guard carrier-agnostically. `as_bind_value` captures the whole
        // structure (a `TermId` IS its structure; a `Value`/`Node` clones cheaply)
        // and never yields a `Path` (that variant is for deferred subst leaves).
        let query = match guard.as_bind_value() {
            BindValue::Term(t) => Value::term(t),
            BindValue::Value(v) => v,
            BindValue::Path(_) => unreachable!("TermView::as_bind_value never yields a Path"),
        };
        let trigger_sorts = self.extract_trigger_sorts(&query);
        let id = ConstraintId(self.guards.len() as u32);
        // Keep any hash-consed leaves alive for the guard's lifetime. Guards are
        // never retracted, so this incref is matched by no decref (as before).
        let mut grounds = Vec::new();
        collect_value_ground_terms_into(self, &query, &mut grounds);
        for t in grounds {
            self.terms.incref(t);
        }
        for &s in &trigger_sorts {
            self.guards_by_sort.entry(s).or_default().push(id.index());
        }
        self.guards.push(Guard {
            id,
            query,
            kind: GuardKind::General,
            trigger_sorts,
            label,
        });
        id
    }

    /// Empty if reflect stdlib not loaded — guard then triggers on no sorts.
    fn extract_trigger_sorts(&mut self, guard: &crate::eval::value::Value) -> Vec<Symbol> {
        let syms = execute::LogicalQuerySymbols::resolve(self);
        let mut out = Vec::new();
        self.collect_trigger_sorts(guard, &syms, &mut out);
        out
    }

    /// Carrier-agnostic structural walk (WI-023): reads the `LogicalQuery` through
    /// [`TermView`](term_view::TermView), so a `TermId` and a `Value::Node`
    /// occurrence carrying the same query extract identical trigger sorts.
    fn collect_trigger_sorts(
        &mut self,
        view: &crate::eval::value::Value,
        syms: &execute::LogicalQuerySymbols,
        out: &mut Vec<Symbol>,
    ) {
        use term_view::{TermView, ViewHead};
        let head = TermView::head(view, self);
        let Some(functor) = head.functor_sym() else { return };

        if Some(functor) == syms.pattern_query {
            let inner = TermView::named_arg(view, self, syms.term).map(|c| c.to_value());
            if let Some(inner) = inner {
                if let Some(sort) = self.view_to_trigger_sort(&inner) {
                    if !out.contains(&sort) {
                        out.push(sort);
                    }
                }
            }
            return;
        }

        if Some(functor) == syms.sort_query {
            // WI-632: `sort_query` carries the sort BY REFERENCE (a `Term::Ref`),
            // so the trigger sort is its already-qualified functor symbol — no
            // runtime name-string resolution.
            let sym = TermView::named_arg(view, self, syms.sort)
                .map(|c| c.to_value())
                .and_then(|v| crate::eval::eval::value_functor(self, &v));
            if let Some(sym) = sym {
                if !out.contains(&sym) {
                    out.push(sym);
                }
            }
            return;
        }

        // Recurse into every structural child (named then positional). Own each
        // child as a `Value` before recursing so no borrow of `self` is held.
        let pos_arity = match &head {
            ViewHead::Functor { pos_arity, .. } => *pos_arity,
            _ => 0,
        };
        for k in TermView::named_keys(view, self) {
            let child = TermView::named_arg(view, self, k).map(|c| c.to_value());
            if let Some(child) = child {
                self.collect_trigger_sorts(&child, syms, out);
            }
        }
        for i in 0..pos_arity {
            let child = TermView::pos_arg(view, self, i).map(|c| c.to_value());
            if let Some(child) = child {
                self.collect_trigger_sorts(&child, syms, out);
            }
        }
    }

    /// The sort a fact head is FILED UNDER.
    ///
    /// Two arms, because a head need not be a constructor at all:
    /// [`Self::sort_of_constructor`] is total over constructors (a variant's
    /// enclosing sort; for §6.3's wrapped entity, itself), and a plain sort name
    /// heading a fact answers as itself. A constructor never reaches the second
    /// arm.
    ///
    /// The second arm reads the name's own CATEGORIES rather than a separate
    /// sort registration, so a free-standing entity needs nothing registered for
    /// it beyond what its declaration already says. It asks `has_kind`, never
    /// `kind_of`: the latter reports only the first-declared category, and the two
    /// §6.3 spellings declare Sort and Entity in opposite order, so it would make
    /// the answer depend on which keyword was written.
    pub fn sort_of_head(&self, functor: Symbol) -> Option<Symbol> {
        if let Some(sort) = self.sort_of_constructor(functor) {
            return Some(sort);
        }
        // Not a constructor at all — a plain sort name heading a fact answers as
        // itself. (A constructor never reaches here: the relation above is total.)
        self.has_kind(functor, crate::intern::SymbolKind::Sort).then_some(functor)
    }

    fn view_to_trigger_sort(&mut self, view: &crate::eval::value::Value) -> Option<Symbol> {
        let functor = term_view::TermView::head(view, self).functor_sym()?;
        self.sort_of_head(functor)
    }

    /// The sort a fact with this head triggers guards on / is indexed by — its
    /// head functor's parent sort (for a constructor), else the functor itself
    /// as a sort. The runtime-assert (`reflect.KB.assert`) counterpart of the
    /// trigger sort the loader computes for a constraint via
    /// [`view_to_trigger_sort`](Self::view_to_trigger_sort), so an asserted fact
    /// and a registered guard agree on the sort key. `None` when the head names
    /// no sort.
    pub fn fact_trigger_sort(&mut self, head: &crate::eval::value::Value) -> Option<Symbol> {
        self.view_to_trigger_sort(head)
    }

    /// Number of registered guards.
    pub fn guard_count(&self) -> usize {
        self.guards.len()
    }

    /// WI-652 — every registered constraint/guard's `LogicalQuery` (cloned), for
    /// the load-time unbacked-eq check. Guards live outside `self.rules`, so
    /// `live_rule_ids` never visits them; this exposes their bodies for a
    /// carrier-agnostic `TermView` walk.
    pub(crate) fn guard_queries(&self) -> Vec<crate::eval::value::Value> {
        self.guards.iter().map(|g| g.query.clone()).collect()
    }

    /// Sorts whose facts re-fire guard `cid`.
    pub fn guard_trigger_sorts(&self, cid: ConstraintId) -> &[Symbol] {
        self.guards.get(cid.index())
            .map(|g| g.trigger_sorts.as_slice())
            .unwrap_or(&[])
    }

    /// Assert a fact with guard checking.
    /// Returns Some(rule_id) if all guards pass, None if any guard is violated.
    ///
    /// WI-922: `trigger_sort` and `clause_kind` are two different things and
    /// used to be one parameter. It was read BOTH as the `guards_by_sort` key
    /// (a declared sort, from `fact_trigger_sort` / a guard's `trigger_sorts`)
    /// and as the stored clause's kind. Both callers pass a real sort, so the
    /// guard lookup was the correct reading and every fact asserted here was
    /// filed under a *sort* where every other clause in the KB carries a KIND —
    /// a fourth instance of the conflation WI-922 is about, and one no load-time
    /// census could see, since it fires only on a runtime extent write.
    pub fn assert_checked(
        &mut self,
        term: TermId,
        clause_kind: ClauseKind,
        trigger_sort: Symbol,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> Option<RuleId> {
        let guard_indices: Vec<usize> = self.guards_by_sort
            .get(&trigger_sort)
            .cloned()
            .unwrap_or_default();

        if guard_indices.is_empty() {
            return Some(self.assert_fact(term, clause_kind, domain, meta));
        }

        // General path: insert tentatively, check guards, retract on failure.
        // Carrier-agnostic: the guard is read through `TermView` (WI-023).
        let rule_id = self.assert_fact(term, clause_kind, domain, meta);

        for &idx in &guard_indices {
            let query = self.guards[idx].query.clone();
            // WI-518: `evaluate_guard` resolves the constraint outright — occurrence
            // (`Value::Node`) leaves now resolve through `resolve_goals` like term
            // leaves, so there is no longer a gated outcome to defer here.
            match self.evaluate_guard(&query) {
                Ok(GuardStatus::Holds) => {}
                Ok(GuardStatus::Violated) => {
                    self.retract(rule_id);
                    return None;
                }
                // WI-628: the guard's search truncated at the depth limit — we
                // cannot CONFIRM this fact preserves the invariant. An integrity
                // guard must never admit a fact it cannot verify, so REJECT
                // (retract) rather than decide from an incomplete search. The
                // load-time path surfaces this loudly as `ConstraintUndecidable`;
                // this per-assert path returns `Option<RuleId>` with no error
                // channel, so it rejects AND emits a loud diagnostic — dropping
                // `reason` silently would make an undecidable rejection read
                // identically to a real `Violated` (the loud-over-silent rule).
                Ok(GuardStatus::Undecidable(reason)) => {
                    let label = self.guards[idx].label.clone();
                    eprintln!(
                        "anthill: integrity constraint{} undecidable within the resolver \
                         depth budget ({}) — fact rejected (an integrity guard must not \
                         admit a fact it cannot verify)",
                        load::label_suffix(&label), reason,
                    );
                    self.retract(rule_id);
                    return None;
                }
                // WI-513: an unsupported-form lowering error on this per-assert
                // runtime path is an internal invariant violation — the post-load
                // `check_all_guards` pass makes such a constraint load-BLOCKING, so a
                // KB never finishes loading with one registered. Reaching it here
                // means a guard was registered without going through that check (a
                // programmer error, not user input). Retract and surface loudly.
                Err(e) => {
                    self.retract(rule_id);
                    let label = self.guards[idx].label.clone();
                    panic!(
                        "assert_checked: integrity constraint{} uses an unsupported \
                         LogicalQuery form ({}) — should have been rejected as \
                         load-blocking by check_all_guards (WI-513)",
                        load::label_suffix(&label), e,
                    );
                }
            }
        }

        Some(rule_id)
    }

    /// Evaluate every registered guard against the current KB — the WI-023
    /// post-load constraint check. Carrier-agnostic: each guard is read through
    /// [`TermView`](term_view::TermView).
    pub fn check_all_guards(&mut self) -> Vec<GuardCheck> {
        let mut out = Vec::with_capacity(self.guards.len());
        for idx in 0..self.guards.len() {
            let query = self.guards[idx].query.clone();
            let label = self.guards[idx].label.clone();
            // WI-513: `evaluate_guard` lowers the constraint through the shared
            // carrier-neutral `lower_query`, which surfaces an unsupported
            // LogicalQuery form (unknown ctor / non-goal leaf) loudly as a
            // `LowerError` rather than silently treating it as vacuously true.
            // WI-518: occurrence (`Value::Node`) leaves resolve like term leaves.
            match self.evaluate_guard(&query) {
                Ok(GuardStatus::Holds) => out.push(GuardCheck::Holds),
                Ok(GuardStatus::Violated) => out.push(GuardCheck::Violated(label)),
                // WI-628: a truncated-search verdict is neither Holds nor
                // Violated — route it to a load-BLOCKING error, not a silent pass.
                Ok(GuardStatus::Undecidable(reason)) => {
                    out.push(GuardCheck::Undecidable(label, reason.to_string()))
                }
                Err(e) => out.push(GuardCheck::Unsupported(label, e.to_string())),
            }
        }
        out
    }

    /// Read a named child of a `LogicalQuery` view as an owned, carrier-agnostic
    /// `Value` (dropping any borrow of `self`).
    fn guard_child(&mut self, view: &crate::eval::value::Value, field: Symbol) -> Option<crate::eval::value::Value> {
        term_view::TermView::named_arg(view, self, field).map(|c| c.to_value())
    }

    /// Evaluate a `LogicalQuery` guard (read through `TermView`): `Ok(true)` if it
    /// holds, `Ok(false)` if violated, `Err(LowerError)` if the constraint uses a
    /// LogicalQuery form the shared lowerer cannot handle (WI-513 — surfaced loudly
    /// instead of vacuously holding). Carrier-agnostic — occurrence (`Value::Node`)
    /// and term leaves both resolve through `resolve_goals` (WI-518). Quantifier
    /// dispatch compares interned [`LogicalQuerySymbols`] (no per-node `String`).
    fn evaluate_guard(&mut self, guard: &crate::eval::value::Value) -> Result<GuardStatus, execute::LowerError> {
        let syms = execute::LogicalQuerySymbols::resolve(self);
        let Some(functor) = term_view::TermView::head(guard, self).functor_sym() else {
            // A bare leaf as a whole guard is not a quantified constraint we
            // enforce — it vacuously holds.
            return Ok(GuardStatus::Holds);
        };
        let f = Some(functor);
        if f == syms.lone_q {
            self.eval_count_guard(guard, &syms, 0, 1)
        } else if f == syms.one_q {
            self.eval_count_guard(guard, &syms, 1, 1)
        } else if f == syms.some_q {
            self.eval_count_guard(guard, &syms, 1, usize::MAX)
        } else if f == syms.no_q {
            self.eval_count_guard(guard, &syms, 0, 0)
        } else if f == syms.forall_q {
            self.eval_forall_guard(guard, &syms)
        } else if f == syms.negation {
            self.eval_negation_guard(guard, &syms)
        } else {
            // Any other constructor — a top-level `pattern_query` / `conjunction`
            // from a NON-quantified constraint, or an unsupported kind — is not
            // ENFORCED (vacuously holds), but we still LOWER it so an unsupported
            // form surfaces as `Err(LowerError)` rather than silently passing
            // (WI-513). `.map(|_| Holds)` discards the goals: we validate the form,
            // we don't run the constraint.
            self.lower_query_with(guard, &syms).map(|_| GuardStatus::Holds)
        }
    }

    /// Evaluate a counting quantifier guard (lone_q, one_q, some_q, no_q).
    fn eval_count_guard(
        &mut self,
        guard: &crate::eval::value::Value,
        syms: &execute::LogicalQuerySymbols,
        min: usize,
        max: usize,
    ) -> Result<GuardStatus, execute::LowerError> {
        let condition = self.guard_child(guard, syms.condition);
        let body = self.guard_child(guard, syms.body);

        let mut goals: Vec<crate::eval::value::Value> = Vec::new();
        if let Some(c) = &condition {
            goals.extend(self.lower_query_with(c, syms)?);
        }
        if let Some(b) = &body {
            // empty_query produces no goals — treat as trivially true
            goals.extend(self.lower_query_with(b, syms)?);
        }

        if goals.is_empty() {
            // No goals means trivially satisfied; count depends on context
            return Ok(GuardStatus::from_holds(min == 0));
        }

        let config = resolve::ResolveConfig {
            // One extra to detect overflow. `saturating_add` guards `some_q`,
            // whose `max` is `usize::MAX` (an unbounded upper bound) — a plain
            // `+ 1` would overflow-panic in debug / wrap to 0 (= unlimited) in
            // release.
            max_solutions: max.saturating_add(1),
            // WI-519: count only DEFINITE solutions — a floundered residual
            // (an undischarged goal) must not inflate the quantifier count.
            definite_only: true,
            ..resolve::ResolveConfig::default()
        };
        let (solutions, truncated) = self.resolve_goals_with_truncation(goals, &config);
        let count = solutions.len();
        // WI-628: a TRUNCATED search UNDERCOUNTS — branches abandoned at the
        // depth limit could hold more solutions — so the true count lies in
        // `[count, ∞)`. The verdict `min ≤ n ≤ max` is trustworthy only when
        // truncation cannot flip it across that whole interval (n only grows):
        //   - known VIOLATED iff `count > max` (already over; stays over)
        //   - known HOLDS    iff `count ≥ min` AND `max` is unbounded (stays in)
        // Otherwise the depth cut leaves the count UNDECIDED — e.g. a `no_q`
        // (max = 0) that found nothing might have missed a witness, and a
        // `one_q` (max = 1) that found exactly one might have missed a second.
        let known_violated = count > max;
        let known_holds = count >= min && max == usize::MAX;
        if truncated && !known_violated && !known_holds {
            return Ok(GuardStatus::Undecidable(
                "counting-quantifier constraint undecidable within depth budget",
            ));
        }
        Ok(GuardStatus::from_holds(count >= min && count <= max))
    }

    /// Evaluate forall_q(var, condition, body): condition AND body must hold
    /// for all solutions. Equivalent to: no solutions of (condition AND NOT body).
    fn eval_forall_guard(
        &mut self,
        guard: &crate::eval::value::Value,
        syms: &execute::LogicalQuerySymbols,
    ) -> Result<GuardStatus, execute::LowerError> {
        let condition = self.guard_child(guard, syms.condition);
        let body = self.guard_child(guard, syms.body);

        // forall x: P -: Q ≡ no x: P -: not(Q)
        let mut goals: Vec<crate::eval::value::Value> = Vec::new();
        if let Some(c) = &condition {
            goals.extend(self.lower_query_with(c, syms)?);
        }
        if let Some(b) = &body {
            let body_goals = self.lower_query_with(b, syms)?;
            if !body_goals.is_empty() {
                // Negate each body goal: `not(g)`, carrier-faithful (WI-518) — `g`
                // may be a Term or an occurrence Node. Use the QUALIFIED NAF builtin
                // symbol `anthill.reflect.not` (`syms.not`), the SAME symbol the
                // shared lowerer's `negation` arm uses, so `get_builtin_view`
                // classifies the goal as `BuiltinTag::Not` and NAF fires. A bare
                // `intern("not")` is a DIFFERENT, unregistered symbol — `not(g)`
                // would then resolve as an ordinary unmatched predicate (0
                // solutions), so a VIOLATED forall would silently "hold" (the
                // loud-over-silent rule's classic failure). Loud if reflect's `not`
                // is unavailable, mirroring the `negation` arm.
                let not_sym = syms.not.ok_or(execute::LowerError::NotYetImplemented(
                    "forall body negation without loaded anthill.reflect.not",
                ))?;
                for g in body_goals {
                    goals.push(self.make_goal_value(not_sym, vec![g]));
                }
            }
        }

        if goals.is_empty() {
            return Ok(GuardStatus::Holds);
        }

        // If any DEFINITE solution exists, the forall is violated. WI-519: a
        // floundered residual must NOT count — counting it would report the
        // forall violated on an undecided (undischarged) witness.
        let config = resolve::ResolveConfig {
            max_solutions: 1,
            definite_only: true,
            ..resolve::ResolveConfig::default()
        };
        let (solutions, truncated) = self.resolve_goals_with_truncation(goals, &config);
        // WI-628: a DEFINITE witness (non-empty) violates the forall regardless of
        // truncation; an EMPTY result from a truncated search is UNDECIDED — the
        // violating `(P ∧ not Q)` witness may lie in a branch cut at the depth
        // limit — so it must NOT read as "holds". (step_naf flipped exactly this
        // case from wrongly-VIOLATED to silently-HOLDS via the synthesized
        // `not(Q)`, whose inner truncation now taints this outer search through
        // WI-628(b); `from_emptiness` catches it.)
        Ok(GuardStatus::from_emptiness(
            solutions.is_empty(),
            truncated,
            "forall constraint undecidable within depth budget",
        ))
    }

    /// Evaluate negation(query): the inner query must have no solutions.
    fn eval_negation_guard(
        &mut self,
        guard: &crate::eval::value::Value,
        syms: &execute::LogicalQuerySymbols,
    ) -> Result<GuardStatus, execute::LowerError> {
        let inner = self.guard_child(guard, syms.query);

        if let Some(inner) = &inner {
            let goals = self.lower_query_with(inner, syms)?;
            if goals.is_empty() {
                // negation of empty_query (always true) = false
                return Ok(GuardStatus::Violated);
            }
            let config = resolve::ResolveConfig {
                max_solutions: 1,
                // WI-519: only a DEFINITE inner solution refutes the negation; a
                // floundered residual is undecided, not a refutation.
                definite_only: true,
                ..resolve::ResolveConfig::default()
            };
            let (solutions, truncated) = self.resolve_goals_with_truncation(goals, &config);
            // WI-628: negation holds iff the inner query has no DEFINITE solution;
            // but an empty result from a TRUNCATED search is UNDECIDED (the
            // refuting solution may sit past the depth cut), so it must NOT read as
            // "negation holds". `from_emptiness` owns that truncated-and-empty
            // check so it cannot be forgotten.
            Ok(GuardStatus::from_emptiness(
                solutions.is_empty(),
                truncated,
                "negation constraint undecidable within depth budget",
            ))
        } else {
            Ok(GuardStatus::Holds)
        }
    }

    pub fn assert_fact(
        &mut self,
        term: TermId,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        // WI-233: O(1) ground-fact dedup. Pre-WI-233 this was a linear
        // scan over every clause sharing the sort, which approached O(N²) total work
        // across many same-sort facts (~180 entries scanned per call
        // on the stdlib load; ~224 per call for the project workitem
        // set). At current N the wins are in the noise (~1-2ms in
        // release) but the algorithmic improvement matters as workitem
        // sets grow.
        // A retracted entry stays in the map, so a re-assert after retract
        // allocates a fresh slot rather than returning the dead RuleId; callers
        // wanting to revive the fact go through `assert_rule` directly.
        // `live_dedup_hit` owns that rule for both indexes.
        if let Some(rid) =
            live_dedup_hit(&self.fact_dedup, &self.rules, &(term, clause_kind, domain))
        {
            return rid;
        }
        self.assert_rule(term, vec![], clause_kind, domain, meta)
    }

    /// Assert a value fact — a fact whose head is carrier-agnostic and may
    /// carry a `Value::Node` (denoted) subterm (WI-348 Phase B). A `Value::Term`
    /// head is an ordinary ground fact and routes to [`Self::assert_fact`]
    /// (hash-consed dedup + refcount). A `Node`/`Entity`-bearing head is stored
    /// directly: indexed by functor via its `TermView` and inserted into the
    /// discrimination tree through the value carrier.
    ///
    /// WI-472: a `Node`/`Entity` head is now ALSO dedup-indexed, closing the
    /// WI-348 Node-head dedup-miss, so two structurally-identical value facts
    /// collapse to one `RuleEntry` exactly as two identical `Term` facts do. Its
    /// key is *derived* — WI-815 makes it the head's carrier-agnostic `GoalKey`
    /// fingerprint in `value_fact_dedup`, where it used to be a materialized
    /// hash-consed `TermId` sharing `fact_dedup`. A head with no usable key falls
    /// back to store-without-dedup. See [`Self::value_fact_dedup_key`].
    pub fn assert_fact_value(
        &mut self,
        head: crate::eval::value::Value,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        use crate::eval::value::Value;
        if let Value::Term { id: t, .. } = head {
            return self.assert_fact(t, clause_kind, domain, meta);
        }
        if let Some(key) = self.value_fact_dedup_key(&head) {
            // Built once and MOVED through both uses: a probe that misses hands its
            // tuple straight to the insert. Nothing clones the key — `retract`
            // re-derives it rather than reading a stash, which is what let the
            // `RuleEntry` field go (WI-815; see `retract`).
            let map_key = (key, clause_kind, domain);
            if let Some(rid) = live_dedup_hit(&self.value_fact_dedup, &self.rules, &map_key) {
                return rid;
            }
            // Miss (or the keyed entry is stale-retracted): store + re-key. Use
            // `insert` (not `or_insert`) so a stale retracted key re-points to the
            // fresh live RuleId.
            let rid = self.push_value_head_entry(head, Vec::new(), clause_kind, domain, meta);
            self.value_fact_dedup.insert(map_key, rid);
            return rid;
        }
        // No usable key (an `Opaque`-bearing head): store without dedup, as
        // before — a dedup-miss, never unsound (WI-348 Phase B).
        self.push_value_head_entry(head, Vec::new(), clause_kind, domain, meta)
    }

    /// WI-472/WI-815: the `value_fact_dedup` key for a `Node`/`Entity`-carrier
    /// ground-fact head — its carrier-agnostic [`GoalKey`](term_view::GoalKey)
    /// structural fingerprint, or `None` when that key would not be injective.
    ///
    /// CARRIER-NEUTRAL, AND THAT IS THE POINT (WI-815). This used to MATERIALIZE
    /// the head into a hash-consed `TermId` (`cached_term` / `value_to_term`),
    /// which cost `&mut self` for a pure question, pinned a term-store `+1` for the
    /// KB's life, and inherited `occurrence_to_term`'s goal-position partiality.
    /// [`goal_fingerprint`](term_view::goal_fingerprint) walks ANY carrier through
    /// `TermView` with `&self` and no store allocation — the move the resolver's
    /// `seen_goals` already made (WI-348), reused rather than restated. Full
    /// history in `docs/design/value-facts-carrier-agnostic-resolver.md` §Delivered.
    ///
    /// WHY THE GUARD IS AN INJECTIVITY GUARD. Over-dedup DROPS a fact (returns the
    /// existing RuleId, never storing the duplicate), so the key must be faithful:
    /// two heads may share one only if they ARE the same fact. A `GoalKey` is an
    /// exact `Vec<StructToken>` with derived `Eq`/`Hash`, not a digest, so this
    /// reduces to [`GoalKey::is_opaque_free`](term_view::GoalKey::is_opaque_free) —
    /// `Opaque` being the one token that carries no payload.
    ///
    /// **THE ONE KNOWN HOLE IS CLOSED (WI-1013), and how it was described was wrong
    /// twice.** `occ_head`'s `Expr::Apply` arm dropped `type_args`, so two `Apply`s
    /// differing ONLY there fingerprinted identically with no `Opaque` token and
    /// `is_opaque_free` answered `true` on a key that was not injective. Both
    /// dismissals of it were false. (1) "No producer mints a `type_args`-bearing
    /// `Apply`" (WI-472): the TYPER does, on every field projection — WI-759's
    /// `synthesize_field_access` rewrites `?x.y` into `field_access[Name = …](?x, "y")`,
    /// 23 times in the stdlib alone. (2) "WI-839 is what would make it reachable"
    /// (WI-1013's own filing): WI-839 REFUSED a written bracket at every position
    /// except an operation-body call, so it narrowed the surface rather than widening
    /// it. What kept the hole from costing a dropped FACT here was narrower than
    /// either claim — a value-fact head is built from a fact/rule position, and a
    /// bracket there is a load error. The bracket is a child on both carriers now, so
    /// the question no longer arises. Closing it belonged to `occ_head` (the same
    /// `TermView` layer `Self::incref_value_ground` documents), and that is where it
    /// happened.
    ///
    /// THE OLD `Bottom` REJECTION, MADE TOTAL. Scanning the whole key rather than
    /// the root catches a lossy child nested in an `Entity` (`value_to_term`'s
    /// `Value::Node` arm mapped one to `Bottom` WITHOUT propagating, so such a head
    /// lowered to `Fn{f, [Bottom]}` and passed a root-only check), and it holds in
    /// RELEASE, where the old path's `debug_assert!(false)` did nothing. `Bottom`
    /// itself is no longer rejected and must not be — under `TermView` it is a real
    /// `⊥` leaf (`Expr::Bottom`, WI-520), not a conversion failure, and the shapes
    /// that used to reify to it (`If`/`Let`/`Match`/`Lambda`) now read as their
    /// structural reflect-`Expr` twins (WI-814) and key faithfully.
    ///
    /// `is_cacheable`'s flex-var exclusion is deliberately NOT adopted, though the
    /// ticket proposed sharing that predicate whole. It is the query cache's extra
    /// condition, not an injectivity one: heads holding DIFFERENT `Global` vars get
    /// different `Var` tokens and stay distinct anyway, so adopting it would turn
    /// every var-bearing head (the loader's omitted-field fresh fills) into a dedup
    /// MISS the `TermId` key did not have.
    ///
    /// A THIRD PREDICATE ANSWERS A NEIGHBOURING QUESTION — `discrim::view_is_indexable`,
    /// "does this head carry a discrimination key?", which also rejects `Opaque` but
    /// additionally rejects functor-less aggregates that key here perfectly well. It
    /// is not shared because the two failure modes differ: an unindexable head is
    /// REFUSED (the discrim insert walk panics), whereas an unkeyable head must only
    /// DEGRADE — WI-348's contract is that a head this function cannot key is stored
    /// un-deduped, never rejected.
    ///
    /// THE ORDER IS THIS GUARD FIRST, THE PANIC SECOND — stated because an earlier
    /// draft of this note had it backwards, and the inverted version is exactly the
    /// reasoning that would justify deleting `is_opaque_free` as unreachable.
    /// `assert_fact_value` calls THIS function, and only a head that gets past it
    /// reaches `push_value_head_entry` and the panicking insert. So the degrade
    /// genuinely runs; what makes it unobservable today is that the panic follows it
    /// for the same heads, not that the panic precedes it.
    ///
    /// A `Value::Term` head never reaches here — [`Self::assert_fact_value`] routes
    /// it to [`Self::assert_fact`] first — but no carrier is special-cased: the
    /// fingerprint is total, so any `Opaque`-bearing head degrades to no-dedup (a
    /// MISS: stored, just not collapsed — never unsound) and everything else keys.
    fn value_fact_dedup_key(
        &self,
        head: &crate::eval::value::Value,
    ) -> Option<term_view::GoalKey> {
        let key = term_view::goal_fingerprint(self, head, &subst::Substitution::new());
        (key.is_opaque_free() && key.has_named_functors()).then_some(key)
    }

    /// Assert a fact `functor(pos…, named…)` from carrier-agnostic `Value`
    /// children, choosing the carrier once (WI-366). If every child is a ground
    /// `Value::Term`, the head is the hash-consed `Term::Fn` and routes to
    /// [`Self::assert_fact`] (dedup + structural sharing); if any child carries a
    /// `Value::Node` (a denoted value-in-type), the head is a `Value::Entity`
    /// value fact via [`Self::assert_fact_value`]. Collapses the
    /// build-Term-or-Entity choice the sort-relation producers (`SortAlias` /
    /// `SortRequiresInfo` / `SortProvidesInfo`) otherwise repeat.
    pub fn assert_fact_carrier(
        &mut self,
        functor: Symbol,
        pos: Vec<crate::eval::value::Value>,
        named: Vec<(Symbol, crate::eval::value::Value)>,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        use crate::eval::value::Value;
        // One source of the carrier decision, shared with [`Self::reify`]: the
        // all-ground head rides as a hash-consed `Term::Fn` (dedup + sharing) and
        // a `Value::Node`-bearing one as a `Value::Entity` value fact. Routing on
        // the assembled carrier keeps the two paths from ever disagreeing.
        match self.fn_value(functor, pos, named) {
            Value::Term { id: term, .. } => self.assert_fact(term, clause_kind, domain, meta),
            head => self.assert_fact_value(head, clause_kind, domain, meta),
        }
    }

    // ── WI-630: loud invariant guard for loader-emitted *metadata* facts ──────
    //
    // `resolve()` candidate lookup is sort-blind — the discrimination tree keys
    // on structure, not on the fact's sort (CLAUDE.md Representation note) — so a
    // loader metadata fact whose head functor is a *user* entity/rule functor
    // silently unifies with every var-quantified query or constraint over that
    // functor. That was the WI-515 bug: the loader asserted `edge(from: <type>,
    // to: <type>)` (the entity's *own* functor) as an entity "schema fact", and
    // the self-referential constraint `no ?p -: edge(from: ?p, to: ?p)` matched
    // it (`?p = Node` in both slots), spuriously violated on self-loop-free data.
    // WI-515 removed that one fact; this seam enforces the invariant for the
    // *class* so a future emission cannot silently re-create the pollution.
    //
    // Every loader declaration-record emission (EntityInfo, SortInfo,
    // MemberInfo, DescriptionInfo, OperationInfo, OperationImpl, Implementation, ProofRecord,
    // Sort{Provides,Requires}Info, SortAlias) routes through these three seams.
    // The check is a **debug-only tripwire** (`cfg(debug_assertions)`): it fires
    // in dev/test builds if a head functor is not a recognized system-metadata
    // functor, and is compiled out entirely in release. This matches the ticket's
    // "load-time debug check" — the guard protects against a *loader-code*
    // mistake, never user input (user `fact` heads bypass this seam entirely), so
    // it is a development-time invariant, not a runtime validation. In release the
    // seams are thin pass-throughs to the plain `assert_fact*` methods.
    //
    // NOT routed here (correctly): user `fact` heads (`load_fact`), the
    // sort/namespace *existence* facts (head is the sort/namespace's own identity
    // — not a data predicate the user constrains), and the `eq(op(…), body)`
    // operation-definition equations (a *rule*, shielded from structural
    // var-queries by `BuiltinTag::SemEq` dispatch — WI-627).

    /// Functor symbol at the head of a term (`Fn` / `Ref` / `Ident`), or `None`
    /// for a non-functor head (`Var`, `Const`, …). One place for the extraction
    /// the metadata seams and [`Self::emit_entity_info`](crate::kb::load) share.
    pub(crate) fn head_functor(&self, tid: TermId) -> Option<Symbol> {
        match self.get_term(tid) {
            Term::Fn { functor, .. } => Some(*functor),
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            _ => None,
        }
    }

    /// Positional arity of the head application at `tid` — 0 for a bare
    /// `Ref` / `Ident` or any non-`Fn` head. Companion to [`Self::head_functor`]
    /// for the arity-aware scoping-marker check (WI-878): a marker NAME at a
    /// non-marker arity (`some_in/1`) is a user typo, not the resolver's 3-ary
    /// quantifier, so it must NOT take the marker exemption in
    /// [`Self::undefined_query_functor`].
    pub(crate) fn head_pos_arity(&self, tid: TermId) -> usize {
        match self.get_term(tid) {
            Term::Fn { pos_args, .. } => pos_args.len(),
            _ => 0,
        }
    }

    /// The head functor of a query pattern `tid` WHEN it is a concrete name the
    /// KB does not define — no rule or fact indexes it and no declaration of any
    /// kind (sort / entity constructor / operation / const / builtin) names it.
    /// `Some(sym)` is the caller's cue to refuse the query LOUDLY rather than hand
    /// it to resolution, which answers an undefined predicate with a silent empty
    /// set indistinguishable from a known functor that merely has no matching
    /// facts — reading as "no such fact" when the truth is "that name resolves to
    /// nothing" (WI-754).
    ///
    /// `None` is returned for the three cases that must NOT be refused:
    ///   * a head with no functor at all (`Var` / `Const` / `Bottom` — a bare
    ///     `?x` or a literal is a legitimate pattern the resolver answers empty);
    ///   * a functor that IS defined;
    ///   * a resolver SCOPING MARKER (`forall_in` / `some_in` / `forall_impl`
    ///     at arity 3, `__pop_assumption` at arity 1) — the resolver recognises
    ///     these by short name AND arity and skolemises / expands them in place,
    ///     so they carry no rule / fact / declaration yet are not unknown. A
    ///     bounded-quantifier query that evaluates to FALSE produces zero
    ///     solutions, and without this arm that empty result would be mis-refused
    ///     as an unknown functor (WI-027). The arity gate (WI-878) means a marker
    ///     NAME at any OTHER arity — a typo like `some_in(x)` — is NOT exempted
    ///     and IS reported, exactly as the resolver no longer treats it as a
    ///     quantifier; the shared [`crate::kb::resolve::is_scoping_marker`]
    ///     predicate keeps the two in lockstep.
    ///
    /// The `rules_by_functor` disjunct is load-bearing, not redundant with
    /// `kind_of`: a predicate defined PURELY by facts keeps an `Unresolved`
    /// functor (the loader interns undefined data names as-is), so `kind_of`
    /// alone would misread a fact-only predicate as unknown. Builtins are
    /// `Resolved` operations, so `kind_of` already covers them.
    ///
    /// This is NOT a substitute for actually resolving: a predicate reachable
    /// only through a rule body (an arity-0 proposition) can resolve to a
    /// solution while sitting in neither table, so the CLI resolves FIRST and
    /// consults this only to explain a genuinely empty result — never to refuse
    /// before resolution (WI-754).
    pub fn undefined_query_functor(&self, tid: TermId) -> Option<Symbol> {
        let sym = self.head_functor(tid)?;
        if crate::kb::resolve::is_scoping_marker(self.local_name_of(sym), self.head_pos_arity(tid)) {
            return None;
        }
        let defined =
            self.kind_of(sym).is_some() || self.rules_by_functor_iter(sym).next().is_some();
        (!defined).then_some(sym)
    }

    /// Every concrete functor in query pattern `tid` that the KB does not define
    /// AND that sits in a position COMMITTED to its truth — the top-level goal, or
    /// anywhere inside a `not` — so refusing it is correct (WI-863). Generalises
    /// [`Self::undefined_query_functor`] (head only) to catch a nested undefined
    /// predicate whose emptiness NAF would otherwise launder into a WRONG answer:
    /// `not(P)` over an undefined `P` resolves the inner goal to a complete-empty
    /// search, and NAF flips that to a confident `true`, asserting a negation for
    /// a name that does not exist — directly, or a connective deep, `not(P | q)`.
    ///
    /// The walk enters negation scope through `not`, and once inside descends
    /// through every goal connective — a nested `not`, the surface `or` / `and`,
    /// `push_choice`, a bounded quantifier's body — collecting each undefined
    /// functor. It deliberately does NOT descend into a BARE (un-negated)
    /// disjunction or quantifier: an `or` / `push_choice` branch may fail while its
    /// sibling succeeds, and a quantifier body over a possibly-empty collection may
    /// never run, so an undefined name there does not corrupt the (correct) answer
    /// and refusing it would reject a valid query (`push_choice(base(1), absent)`
    /// answers `true`; `forall ?x in []: absent(?x)` is vacuously `true`). `not` is
    /// the one goal context where an undefined functor NECESSARILY falsifies its
    /// negand, so it is the one whose branches are always followed.
    ///
    /// # That tolerance is ABOUT ABSENCE, and does not transfer to an AMBIGUITY
    ///
    /// WI-917 asked whether an AMBIGUOUS name in one of the tolerated positions is
    /// tolerated for the same reason. It is not, and the reason above is what rules
    /// it out: it turns on the branch having no answers to lose. An absent name
    /// genuinely has none, so leaving it to resolution costs nothing. A CONTESTED
    /// name has answers under EITHER reading, and the bare intern the pattern binds
    /// it to (WI-476) has none — so tolerating one silently DROPS solutions, which
    /// is exactly the corruption this paragraph promises does not happen. Measured
    /// on the `wi917` CLI fixture, where `contested917` is a rule in two imported
    /// namespaces and each reading answers one row: `push_choice(never917(),
    /// contested917(?v))` printed that row under either import ALONE, and `no
    /// solutions`, exit 0, no diagnostic, under both.
    ///
    /// So an ambiguity is refused wherever it is written, by the separate
    /// [`Self::ambiguous_query_names`] walk. The two questions stay separate
    /// functions because they have opposite descent rules for one reason: this walk
    /// asks what the SEARCH commits to, and an ambiguity is a defect of the TEXT.
    ///
    /// A DATA slot — a constructor argument, `Widget(id: absent(42))` — is never a
    /// goal and is never walked. Each candidate keeps the head-only exemptions
    /// (scoping marker skipped, defined functor skipped) plus the per-node
    /// discrimination-tree backstop (`browse_program_clauses_matching`, as the
    /// CLI's `report_if_unknown_functor` does for the head): an arity-0
    /// proposition reachable only through a rule body sits in no functor table yet
    /// IS declared, so the tree clears it and resolve-first's known-and-false
    /// results still answer. `forall_impl` (not a `query` surface form) and
    /// `ho_apply` (applies a possibly-unbound predicate variable) are not walked.
    pub fn undefined_query_goal_functors(&self, tid: TermId) -> SmallVec<[Symbol; 4]> {
        let mut out = SmallVec::new();
        // The top-level goal commits to its head (WI-754); `under_not` starts
        // false and turns true the moment the walk steps through a `not`.
        self.collect_undefined_goal_functors(tid, false, &mut out);
        out
    }

    /// Recursive worker for [`Self::undefined_query_goal_functors`]. Every node the
    /// walk reaches is in a committed position, so its head is always checked; the
    /// gating is on DESCENT — a bare connective (`under_not` false and head not
    /// `not`) is left to resolution and never entered. `out` dedups. Terminates
    /// because terms are acyclic and every goal child is a strict subterm.
    fn collect_undefined_goal_functors(
        &self,
        tid: TermId,
        under_not: bool,
        out: &mut SmallVec<[Symbol; 4]>,
    ) {
        if let Some(sym) = self.undefined_query_functor(tid) {
            // Discrim backstop, per node — an arity-0 proposition reachable only
            // through a rule body is in no functor table but matches the tree.
            // Ordered cheap-check first: skip the tree walk for a name already
            // recorded from a sibling branch.
            if !out.contains(&sym) && self.browse_program_clauses_matching(&tid).is_empty() {
                out.push(sym);
            }
        }
        // Follow goal branches only inside a negation: `not` opens the scope, and
        // once open every connective within it is followed. A bare disjunction /
        // quantifier is left to resolution (see the type-level doc).
        let entering_not = self.is_negation_functor(tid);
        if under_not || entering_not {
            for child in self.goal_arg_termids(tid) {
                self.collect_undefined_goal_functors(child, true, out);
            }
        }
    }

    /// WI-917: every functor in query pattern `tid` whose name the citing scope
    /// `scope` resolves to TWO OR MORE symbols — the pattern position's half of
    /// the load error a reference gets, and the answer to the tolerance question
    /// stated at [`Self::undefined_query_goal_functors`].
    ///
    /// A contested name arrives here as the WI-476 bare intern: the pattern position
    /// has no error channel, so `load::resolve_query_name` gives an ambiguity and an
    /// absence the SAME term (a symbol that heads no clause) and leaves the DIAGNOSIS
    /// to the caller. Re-reading the ladder at `scope` is what tells them apart —
    /// the same re-read the CLI's head reporter does, here extended to every node.
    ///
    /// EVERY node: a bare disjunction branch, a quantifier body, a data slot — the
    /// positions WI-863 leaves to resolution. Where a name sits decides what an
    /// ABSENT one costs, and nothing about what a contested one costs. The data slot
    /// is where the two diverge most sharply: an absent data name's bare intern is
    /// what the FACT's loader produced too, so pattern and fact match; a contested
    /// one's matches neither reading.
    pub fn ambiguous_query_names(&self, tid: TermId, scope: ScopeId) -> SmallVec<[Symbol; 4]> {
        let mut out = SmallVec::new();
        self.collect_ambiguous_query_names(tid, scope, &mut out);
        out
    }

    /// Recursive worker for [`Self::ambiguous_query_names`]. Descent is
    /// unconditional (`Term::subterms` — positional and named args alike), so unlike
    /// [`Self::collect_undefined_goal_functors`] there is no gate to thread. `out`
    /// dedups. Terminates because terms are acyclic.
    fn collect_ambiguous_query_names(
        &self,
        tid: TermId,
        scope: ScopeId,
        out: &mut SmallVec<[Symbol; 4]>,
    ) {
        // The SAME candidate test as the undefined walk — a scoping marker and a
        // defined functor are dropped by `undefined_query_functor`, and the
        // discrimination-tree backstop clears an arity-0 proposition that is declared
        // but sits in no functor table — so the two refusals cannot disagree about
        // which symbols are even askable. Ordered ladder-read first: an ambiguity is
        // rare and the tree walk is the expensive half.
        if let Some(sym) = self.undefined_query_functor(tid) {
            let ambiguous = matches!(
                load::resolve_name_in_kb(self, self.local_name_of(sym), scope),
                ResolveResult::Ambiguous(_)
            );
            if ambiguous
                && !out.contains(&sym)
                && self.browse_program_clauses_matching(&tid).is_empty()
            {
                out.push(sym);
            }
        }
        for child in self.get_term(tid).subterms() {
            self.collect_ambiguous_query_names(child, scope, out);
        }
    }

    /// True iff `tid`'s head is the negation builtin `not` — the one goal
    /// connective the walk always enters (WI-863).
    fn is_negation_functor(&self, tid: TermId) -> bool {
        matches!(self.head_functor(tid), Some(f) if self.builtin_of(f) == Some(BuiltinTag::Not))
    }

    /// The child `TermId`s of `tid` the resolver evaluates as GOALS — empty for a
    /// plain predicate or data constructor (whose arguments are data, not goals).
    /// The goal connectives: `not`'s negand, the two branches of `push_choice` and
    /// of the surface `or` / `and`, and a bounded quantifier's `tuple(...)` body.
    /// Read for DESCENT only; whether these are followed is gated on negation scope
    /// by [`Self::collect_undefined_goal_functors`].
    fn goal_arg_termids(&self, tid: TermId) -> SmallVec<[TermId; 2]> {
        let Term::Fn { functor, pos_args, .. } = self.get_term(tid) else {
            return SmallVec::new();
        };
        // Recognised by name: a bounded quantifier's body is a `tuple(...)` of
        // goals at arg 2 (the loader always wraps it; `resolve::unwrap_tuple_args`
        // reads the same shape), and `or` / `and` are the kernel disjunction /
        // conjunction RULES (`a | b` lowers to `or(a, b)`) — not builtins, so
        // `builtin_of` would miss them.
        match self.local_name_of(*functor) {
            "forall_in" | "some_in" => {
                return pos_args
                    .get(2)
                    .map(|&body| self.tuple_goal_termids(body))
                    .unwrap_or_default();
            }
            "or" | "and" => return pos_args.iter().take(2).copied().collect(),
            _ => {}
        }
        match self.builtin_of(*functor) {
            Some(BuiltinTag::Not) => pos_args.iter().take(1).copied().collect(),
            Some(BuiltinTag::PushChoice) => pos_args.iter().take(2).copied().collect(),
            _ => SmallVec::new(),
        }
    }

    /// Components of a bounded-quantifier body `tid`: the positional args of its
    /// `tuple(...)` wrapper. A body that is not a tuple is treated as a single
    /// goal (the loader wraps every body, so this is defensive) — returned as-is
    /// rather than dropped, so no goal escapes the walk (loud over silent).
    fn tuple_goal_termids(&self, tid: TermId) -> SmallVec<[TermId; 2]> {
        match self.get_term(tid) {
            Term::Fn { functor, pos_args, .. } if self.local_name_of(*functor) == "tuple" => {
                pos_args.iter().copied().collect()
            }
            _ => SmallVec::from_elem(tid, 1),
        }
    }

    /// True iff `qualified_name` names a reserved system-metadata functor — one
    /// the loader is permitted to head a metadata fact with. The reflect and
    /// realization declaration records live under `anthill.reflect.` /
    /// `anthill.realization.`; the kernel meta functors (`SortAlias`, `meta`)
    /// are registered qualified-only in [`load::register_prelude`] with these
    /// bare qualified names.
    fn is_reserved_metadata_functor_name(qualified_name: &str) -> bool {
        qualified_name.starts_with("anthill.reflect.")
            || qualified_name.starts_with("anthill.realization.")
            || matches!(qualified_name, "SortAlias" | "meta")
    }

    /// True iff facts headed by `functor` are DECLARATION RECORDS — the reflect /
    /// realization vocabulary the loader renders every declaration into
    /// (`EntityInfo`, `SortInfo`, `MemberInfo`, `OperationInfo`, `ProofRecord`, …).
    ///
    /// The one owner of that question, shared with the WI-630 write-side tripwire
    /// [`Self::check_metadata_head`] so the write side and the read side cannot
    /// name different sets (WI-928).
    pub(crate) fn is_metadata_functor(&self, functor: Symbol) -> bool {
        Self::is_reserved_metadata_functor_name(self.qualified_name_of(functor))
    }

    /// WI-630 debug tripwire: panic if `functor` is not a reserved metadata
    /// functor (or is a non-functor head). Compiled out in release — see the
    /// module-level note above.
    #[cfg(debug_assertions)]
    fn check_metadata_head(&self, functor: Option<Symbol>) {
        let ok = functor.map(|f| self.is_metadata_functor(f)).unwrap_or(false);
        if !ok {
            let shown = functor
                .map(|f| self.qualified_name_of(f))
                .unwrap_or("<non-functor head>");
            panic!(
                "WI-630 invariant violated: loader-emitted metadata fact heads \
                 non-reflect functor `{shown}`. A metadata fact under a user data/rule \
                 functor pollutes every var-quantified query over it (resolve() is \
                 sort-blind — see the WI-515 `edge` schema-fact bug). Head metadata \
                 facts with a reserved `anthill.reflect.*` / `anthill.realization.*` \
                 functor, not a user functor."
            );
        }
    }

    /// [`Self::assert_fact`] for a loader metadata fact (WI-630) — see the
    /// module-level note. Debug-only head-functor tripwire, then delegate.
    pub fn assert_metadata_fact(
        &mut self,
        term: TermId,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        #[cfg(debug_assertions)]
        self.check_metadata_head(self.head_functor(term));
        self.assert_fact(term, clause_kind, domain, meta)
    }

    /// [`Self::assert_fact_value`] for a loader metadata fact (WI-630).
    pub fn assert_metadata_fact_value(
        &mut self,
        head: crate::eval::value::Value,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        #[cfg(debug_assertions)]
        {
            use crate::eval::value::Value;
            let functor = match &head {
                Value::Entity { functor, .. } => Some(*functor),
                Value::Term { id, .. } => self.head_functor(*id),
                _ => None,
            };
            self.check_metadata_head(functor);
        }
        self.assert_fact_value(head, clause_kind, domain, meta)
    }

    /// [`Self::assert_fact_carrier`] for a loader metadata fact (WI-630).
    pub fn assert_metadata_fact_carrier(
        &mut self,
        functor: Symbol,
        pos: Vec<crate::eval::value::Value>,
        named: Vec<(Symbol, crate::eval::value::Value)>,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        #[cfg(debug_assertions)]
        self.check_metadata_head(Some(functor));
        self.assert_fact_carrier(functor, pos, named, clause_kind, domain, meta)
    }

    /// Incref the ground `TermId` leaves reachable in a value head (WI-348
    /// Phase B), keeping them alive for the rule's lifetime — including those
    /// carried *inside* a `Value::Node` occurrence (e.g. a `denoted` Type's
    /// `TypeChild::Ground`), which the occurrence builders do NOT refcount
    /// themselves (review #1): without this, a hash-consed term shared with a
    /// term-carrier fact would dangle when that fact is retracted. Walks the
    /// head through `TermView` — the same surface the discrimination tree
    /// indexes — so the owned set matches what is searched.
    ///
    /// Known gap (deferred to the value-fact payoff phase): a field key not yet
    /// interned is not surfaced by `TermView` and so is not owned here. Symmetric
    /// with `release_value_ground`, so balanced regardless.
    ///
    /// A CALL's `type_args` used to be named here too, and no longer belongs: WI-1013
    /// made an `Expr::Apply`'s `[T = …]` bracket a `TermView` child, so its ground
    /// leaves are walked and owned like any other. That is inert today rather than a
    /// fix anyone can observe — a value-fact head is built from a fact/rule position
    /// and a bracket there is a load error (WI-839) — but the gap is gone rather than
    /// deferred, and leaving it listed would send the next reader looking for it.
    fn incref_value_ground(&mut self, v: &crate::eval::value::Value) {
        for t in self.collect_value_ground_terms(v) {
            self.terms.incref(t);
        }
    }

    /// Inverse of [`Self::incref_value_ground`], for retract. Collects the same
    /// multiset (the head Value is immutable once stored), so every incref is
    /// matched by exactly one release.
    fn release_value_ground(&mut self, v: &crate::eval::value::Value) {
        for t in self.collect_value_ground_terms(v) {
            self.terms.release(t);
        }
    }

    /// The ground `TermId` leaves reachable in a value, via `TermView` (so a
    /// `Value::Node` occurrence's ground children are included). Read-only; the
    /// caller increfs / releases the result.
    fn collect_value_ground_terms(&self, v: &crate::eval::value::Value) -> Vec<TermId> {
        let mut out = Vec::new();
        collect_value_ground_terms_into(self, v, &mut out);
        out
    }

    /// Mark a rule/fact as retracted. Removes from active indexes, decrements refcounts.
    pub fn retract(&mut self, id: RuleId) {
        let entry = &mut self.rules[id.index()];
        if entry.retracted {
            return;
        }
        entry.retracted = true;

        let head_val = entry.head.clone();
        let clause_kind = entry.clause_kind;
        let domain = entry.domain;
        let meta = entry.meta;
        // WI-246: body atoms are occurrences with no separate refcount to
        // release; emptiness (fact-ness) reads the occurrence body.
        let is_fact = entry.body_nodes.is_empty();
        let label = entry.label;
        // Remove from indexes
        if let Some(v) = self.by_domain.get_mut(&domain) {
            v.retain(|&rid| rid != id);
        }
        // rules_by_functor via the head's `TermView` functor (any carrier — WI-348).
        // WI-436: `functor_sym` reads a 0-ary constructor's symbol off its bare
        // `Ref(c)` head, so retract removes from the SAME `rules_by_functor` bucket
        // `assert` populated (insert/retract stay symmetric).
        let head_functor = term_view::TermView::head(&head_val, self).functor_sym();
        if let Some(f) = head_functor {
            let removed = if let Some(v) = self.rules_by_functor.get_mut(&f) {
                let before = v.len();
                v.retain(|&rid| rid != id);
                before != v.len()
            } else {
                false
            };
            // WI-812: drop the `has_bodied_rule` gate iff a BODIED rule was actually
            // removed from the bucket. Guarding on `removed` (not just `!is_fact`)
            // keeps the count correct when the rule was already pulled from the
            // bucket by `unindex_functor` (retract then finds nothing to remove).
            if removed && !is_fact {
                self.dec_bodied_rule_count(f);
            }
            // WI-665: a retract flips the simp gate only when the head is an
            // `eq`/`unify` equation — it drops that rule from the bucket
            // `has_directional_rewrite` counts. See
            // `invalidate_simp_gate_if_connective`.
            self.invalidate_simp_gate_if_connective(f);
        }
        if let Some(label_sym) = label {
            if let Some(v) = self.rules_by_label.get_mut(&label_sym) {
                v.retain(|&rid| rid != id);
            }
        }

        // WI-233: ground-fact dedup index. Remove only if this RuleId
        // is the one currently keyed at (head, sort, domain) — a
        // previously-retracted-then-re-asserted fact may have a
        // different RuleId at that key.
        if is_fact {
            // A Term-carrier head keys `fact_dedup` on the head term itself
            // (WI-233); a Node/Entity head keys `value_fact_dedup` on the derived
            // fingerprint. Both removals are rid-guarded by `remove_dedup_entry`.
            // The arms are mutually exclusive: a value head is never `Value::Term`.
            //
            // WI-815: the value key is RE-DERIVED here from the same head, rather
            // than stashed on the `RuleEntry` as WI-472's `Option<TermId>` was.
            // That stash existed because `cached_term` needed `&mut kb`, which
            // retract could not give it at this point; `value_fact_dedup_key` is
            // now `&self`, so the obstacle is gone and with it the reason.
            //
            // WHAT MAKES RE-DERIVING SAFE — stated precisely, because an earlier
            // draft claimed "symmetric by construction" and that is too strong.
            // The key is a function of (head, MUTABLE KB STATE), not of the head
            // alone: `functor_view_head` consults `is_constructor_symbol`,
            // `wrapped_expr_head` / `pattern_head` / `list_literal_functor` consult
            // `try_resolve_symbol`, and `type_node_keys` consults `lookup_symbol` —
            // all of which can answer differently later in a load. So a re-derived
            // key CAN differ from the one inserted.
            //
            // Safety therefore rests on the RID GUARD, not on stability:
            // `remove_dedup_entry` evicts only an entry naming THIS rule, so a
            // drifted key removes nothing and the worst case is an orphan entry
            // pointing at a retracted rule — which `live_dedup_hit` already treats
            // as a miss and `insert` overwrites. Bounded, and the same exposure
            // `remove_ground` ten lines below has had all along (it re-derives the
            // discrim path from this same head), so it is pre-existing rather than
            // introduced here — but it is a leak, not an impossibility. Measured cold: 5 value-fact retracts across
            // the entire 4139-test suite, against ~103k asserts — so a stash would
            // have paid a `GoalKey` deep clone per ASSERT to save five walks.
            match &head_val {
                crate::eval::value::Value::Term { id: head_t, .. } => {
                    remove_dedup_entry(&mut self.fact_dedup, (*head_t, clause_kind, domain), id);
                }
                _ => {
                    if let Some(k) = self.value_fact_dedup_key(&head_val) {
                        remove_dedup_entry(
                            &mut self.value_fact_dedup,
                            (k, clause_kind, domain),
                            id,
                        );
                    }
                }
            }
        }

        // Remove from discrimination tree (before releasing terms). The
        // view-driven walk needs `&self`, so detach the index first (WI-348).
        self.with_discrim_detached(|kb, discrim| {
            discrim.remove_ground(kb, &head_val, &id);
        });

        // Release refcounts (head/sort/domain/meta; the body atoms are
        // occurrences with no term-store refcount of their own — WI-246).
        //
        // WI-815 removed the one exception WI-472 had introduced here: a deduped
        // Node/Entity fact head used to ALSO pin a `+1` on a MATERIALIZED key term
        // (a `Node`'s `cached_term` cache slot, an `Entity`'s `value_to_term`
        // alloc), deliberately not released — pin-for-lifetime, growing by one per
        // retract→re-assert cycle. The key is now a `GoalKey`, which holds no
        // term-store refcount, so "head occurrences hold no term-store refcount"
        // is again true with no exception, and there is nothing for a deferred
        // release queue to reclaim.
        self.release_value_ground(&head_val);
        if let Some(m) = meta {
            self.terms.release(m);
        }
    }

    // ── Sort management ─────────────────────────────────────────

    /// Register a sort NAME with its kind.
    ///
    /// Keyed by `Symbol` like every sibling index. As a `TermId` it carried the
    /// same order-dependent split `sort_entities` did: `register_sort` stored the
    /// spelling `name_to_sort_term` produced at DECLARATION time, while every
    /// probe rebuilt one via `make_name_term_from_sym` — and the WI-511
    /// `Fn{c}`→`Ref(c)` canon is gated on `is_constructor_symbol`, so the two
    /// could differ and `sort_kind` would silently answer `None`.
    pub fn register_sort(&mut self, sort: Symbol, kind: SortKind) {
        self.sort_info.insert(sort, kind);
    }

    /// Record the REFLEXIVE case of belongs-to: `sym` IS its own sort (§6.3's
    /// wrapped entity — `entity E` is `sort E { entity E }`, one symbol).
    ///
    /// Deliberately NOT [`Self::register_entity_of`], which additionally marks the
    /// symbol in `constructor_symbols`. That flag is a different question — it
    /// drives the WI-511 nullary alloc canon (`Fn{c,[],[]}` → `Ref(c)`) — and the
    /// name's own nullary term is also its SCOPE KEY, which `is_sort_scope` matches
    /// only in the `Fn` spelling. Measured: routing this through
    /// `register_entity_of` re-spelled those terms and 24 tests failed with
    /// `expected Type, got WorkItem` — a bare free-standing entity stopped reading
    /// as a type, which is exactly the consequence WI-926 predicted when it
    /// declined to mark the eponymous constructor.
    pub fn register_self_sort(&mut self, sym: Symbol) {
        let children = self.sort_entities.entry(sym).or_default();
        if !children.contains(&sym) {
            children.push(sym);
        }
        self.entity_parent.insert(sym, sym);
    }

    /// Register an entity-of relationship: entity is a constructor of parent sort.
    /// Updates in-memory indexes (sort_entities, entity_parent).
    /// The loader separately asserts EntityOf(entity, parent) facts in the KB.
    pub fn register_entity_of(&mut self, entity: TermId, parent: TermId) {
        // WI-697 keyed the parent index by the constructor's functor SYMBOL,
        // retiring the Fn{c}/Ref(c) TermId dual-keying there — a symbol has ONE
        // spelling, whereas the WI-511 alloc canon (`Fn{c,[],[]}` → `Ref(c)`,
        // gated on `is_constructor_symbol`) is ORDER-DEPENDENT and leaves the
        // same symbol with two TermId identities pre/post registration.
        //
        // `sort_entities` is now keyed and valued the same way, finishing that
        // job. It was the last TermId-keyed half, and the split was REAL, not
        // hypothetical: `Color` was measured registering as a parent under BOTH
        // `Ref(Color)` and `Fn{Color}` on one suite run — two buckets for one
        // sort, so `sort_children` answered differently depending on
        // which spelling the CALLER happened to hold. With symbols there is one
        // bucket and the dedup below is a plain `contains`.
        //
        // Deliberately NOT `name_term_sym`: that requires a NULLARY name, and the
        // match this replaced accepted `Fn { functor, .. }` at ANY arity. The suite
        // shows only nullary entities and parents here, but "not observed in the
        // suite" is not evidence of unreachability — a parameterized `provides`
        // block reaches the loader through paths the suite never ran, and narrowing
        // on that reasoning is what turned one into a process abort. Taking the
        // functor of an applied term keeps the old reading; a non-functor term is
        // still refused loudly, as before.
        let functor_of = |kb: &Self, t: TermId| -> Symbol {
            match *kb.terms.get(t) {
                Term::Fn { functor, .. } => functor,
                Term::Ref(x) | Term::Ident(x) => x,
                _ => panic!(
                    "register_entity_of: term {t:?} has no functor symbol \
                     (entity and parent must be sort/constructor references)"
                ),
            }
        };
        let entity_sym = functor_of(self, entity);
        let parent_sym = functor_of(self, parent);
        // WI-719: `register_entity_of` runs TWICE for each prelude constructor
        // (`some`/`none`/`nil`/`cons`) — once at `register_prelude` bootstrap,
        // once when option/list.anthill's sort body loads — and the two calls can
        // pass DIFFERENT TermId spellings of the same constructor. Deduping keeps
        // `sort_children` from double-counting one constructor.
        let children = self.sort_entities.entry(parent_sym).or_default();
        if !children.contains(&entity_sym) {
            children.push(entity_sym);
        }
        self.constructor_symbols.insert(entity_sym);
        self.entity_parent.insert(entity_sym, parent_sym);
    }

    /// Check if `sub` is an entity of `sup` (1-level entity → parent sort). The
    /// TermId-ergonomic wrapper over [`Self::is_entity_of_view`] for the many
    /// ground-term callers — `TermId` is itself a [`term_view::TermView`], so it
    /// delegates directly (no `Value` wrap).
    pub fn is_entity_of(&self, sub: TermId, sup: TermId) -> bool {
        self.is_entity_of_view(&sub, &sup)
    }

    /// WI-697 — the carrier-neutral core of [`Self::is_entity_of`]: reads both
    /// operands through [`term_view::TermView`] (no reify), so a `Value::Node`
    /// occurrence goal decides without lowering to a term.
    ///
    /// - Reflexive: `views_structurally_equal` — STRUCTURAL, so a parameterized
    ///   `List[Int]` is not conflated with `List[Str]`. (This canonicalizes the
    ///   `Fn{c}`/`Ref(c)` 0-ary spellings via `functor_view_head`, exactly as the
    ///   former builtin's `reify`+`==` did; the retired direct-`TermId` `==` did
    ///   not, so two cross-spelled TermIds of the *same* entity now compare equal —
    ///   a same-direction broadening of the convenience path onto the builtin's
    ///   semantics, unreachable via any caller.)
    /// - Parent lookup keyed on `sub`'s functor symbol (O(1); the symbol unifies
    ///   the Fn/Ref spellings), GATED on a NULLARY head: the `entity_parent` index
    ///   only ever holds nullary entity terms (`register_entity_of` /
    ///   `name_to_sort_term`), so an APPLIED constructor `Fn{c,[args]}` is NOT an
    ///   entity of its sort here — preserving the pre-WI-697 verdict, which keyed on
    ///   the full nullary `TermId` and so missed the applied form.
    pub(crate) fn is_entity_of_view<A: term_view::TermView, B: term_view::TermView>(
        &self,
        sub: &A,
        sup: &B,
    ) -> bool {
        if term_view::views_structurally_equal(self, sub, sup) {
            return true;
        }
        let sub_sym = match sub.head(self) {
            term_view::ViewHead::Ref(s) => s,
            term_view::ViewHead::Functor { functor: Some(s), pos_arity: 0, named_arity: 0 } => s,
            _ => return false,
        };
        // The stored parent is a NAME; `sup` may arrive in any carrier/spelling
        // (`Fn{S}` or `Ref(S)` — WI-511 makes that order-dependent), so compare
        // the two as SYMBOLS rather than structurally.
        let Some(&parent_sym) = self.entity_parent.get(&sub_sym) else { return false };
        match term_view::TermView::head(sup, self) {
            term_view::ViewHead::Ref(s) => s == parent_sym,
            term_view::ViewHead::Functor { functor: Some(s), pos_arity: 0, named_arity: 0 } => {
                s == parent_sym
            }
            _ => false,
        }
    }

    /// The sort a constructor BELONGS TO — TOTAL over constructors (WI-925).
    ///
    /// This is what `entity`-wrapping is for: §6.3 wraps a free-standing `entity E`
    /// into `sort E { entity E }` precisely so that every entity has a sort, so the
    /// relation must actually be total or the wrapping buys nothing. For an
    /// eponymous or free-standing entity the sort IS the entity (WI-926: one
    /// symbol), so the edge is REFLEXIVE — `E`'s sort is `E`.
    ///
    /// Prefer this wherever the question is "which sort does this belong to".
    /// [`Self::strict_parent_sort`] is the STRICT (irreflexive) view, for
    /// walkers that climb the chain.
    pub fn sort_of_constructor(&self, functor: Symbol) -> Option<Symbol> {
        self.entity_parent.get(&functor).copied()
    }

    /// The STRICT parent sort of a constructor — [`Self::sort_of_constructor`]
    /// minus the reflexive case, i.e. the parent that is a *different* symbol.
    /// WI-697: an O(1) lookup into the symbol-keyed index (was an O(n) scan).
    ///
    /// This is the accessor a chain-CLIMBING walker wants, and the single place
    /// the fixpoint is cut. Several walkers recurse `parent(parent(…))` and were
    /// written when "a parent is a sort, never a constructor" made the chain
    /// acyclic by construction; WI-926 made one name both, so that no longer holds
    /// of the stored relation. Returning `None` at the fixpoint keeps every one of
    /// them terminating without each having to re-check `parent == self` — the
    /// alternative being the same guard copied into `sort_provides_admissibly`,
    /// `sort_sym_compatible`, `bare_provider_binding_precise`, and any walker
    /// written later that would simply forget it.
    ///
    /// WI-946 RENAMED this from `constructor_parent_sort`, which named no
    /// restriction and so read as the general belongs-to accessor: five
    /// "which sort does this belong to" readers had reached for it by accident
    /// and each silently answered `None` for an eponymous / free-standing
    /// entity — the shape §6.3 exists to make equivalent to the long form.
    /// The restriction now lives in the name. If you are about to call this,
    /// the question must genuinely be "which DIFFERENT sort is this filed
    /// under"; anything else wants [`Self::sort_of_constructor`].
    pub fn strict_parent_sort(&self, functor: Symbol) -> Option<Symbol> {
        self.entity_parent.get(&functor).copied().filter(|&p| p != functor)
    }

    /// All entity-constructor functor symbols whose parent sort is `sort_sym`
    /// (WI-397). Enumerated from the entity→parent index, which holds every
    /// registered entity; the returned symbols are exactly the
    /// [`Self::entity_field_types`] keys (both the index key and the field-types
    /// key come from `remap_name(entity.name)` — `name_to_sort_term` builds the
    /// `entity_parent` key as `Fn{remap_name(..)}`). Used by the projection
    /// eliminator to resolve a field-access receiver's field type.
    pub fn constructors_of_sort(&self, sort_sym: Symbol) -> Vec<Symbol> {
        let mut out = Vec::new();
        // WI-697: the key IS the constructor symbol, and the value is now the
        // parent's NAME, so this is a direct symbol compare. (Symbol keys are
        // unique, so — unlike the former dual-keyed TermId scan — no
        // per-constructor duplicate is produced.)
        for (&entity_sym, &parent_sym) in &self.entity_parent {
            if parent_sym == sort_sym {
                out.push(entity_sym);
            }
        }
        out
    }

    /// Constructors to inspect when resolving a FIELD of `sort_sym`: its entity
    /// variants ([`Self::constructors_of_sort`]) PLUS `sort_sym` itself when it
    /// is a free-standing entity. A top-level `entity Pose(x, y)` is its own
    /// constructor with no parent sort, so `constructors_of_sort` is empty for
    /// it, yet `entity_field_types(Pose)` holds its fields — the same
    /// free-standing-entity case `check_constructor_iter` handles ("the entity
    /// is its own type"). Field lookups that only walked `constructors_of_sort`
    /// thus missed every field of a free-standing entity (WI-490: a `(p).x` on
    /// such a receiver failed dot dispatch). Self is appended (deduped) so a
    /// normal multi-variant sort — whose own symbol carries no
    /// `entity_field_types` — is unaffected.
    pub fn field_constructors_of_sort(&self, sort_sym: Symbol) -> Vec<Symbol> {
        let mut out = self.constructors_of_sort(sort_sym);
        if self.entity_field_types(sort_sym).is_some() && !out.contains(&sort_sym) {
            out.push(sort_sym);
        }
        out
    }

    /// Does `sort_sym` have any entity constructor — i.e. is it a
    /// constructor-shaped DATA sort rather than an abstract spec? Used by the
    /// provider-info loader (WI-407) to tell `sort QueryableStore { fact Store }`
    /// (Store is an abstract spec → a provider edge) from `sort Holder { fact
    /// Color[..] }` (Color is a data sort with `entity red/green` → a data fact,
    /// NOT a provider edge).
    ///
    /// Reads the SYMBOL TABLE (a direct child symbol of kind `Entity`), not the
    /// runtime `entity_parent` index, ON PURPOSE: `entity_parent` is populated
    /// incrementally as each sort body loads, so a fact processed BEFORE its
    /// referenced sort's body (a forward reference) would see it empty and
    /// misclassify a data sort as a spec. Child symbols are all defined in
    /// `scan_definitions` (pass 1, before any loading), so this answer is
    /// load-order-independent. Mirrors [`Self::type_params_of_sort`]'s
    /// direct-child scan.
    ///
    /// WI-926 (§6.3): an EPONYMOUS constructor is the sort itself, so it is not a
    /// child symbol and the scan alone would answer `false` for
    /// `sort Project { entity Project(…) }` — misclassifying the commonest data
    /// sort as an abstract spec. Its field-name registration answers instead, and
    /// it is written in the SAME pass-1 scan (`register_entity_field_names_scan`),
    /// so this arm keeps the load-order independence the child scan was chosen for.
    pub fn sort_has_constructors(&self, sort_sym: Symbol) -> bool {
        if self.is_entity_constructor(sort_sym) {
            return true;
        }
        let qn = self.qualified_name_of(sort_sym);
        let prefix = format!("{qn}.");
        self.symbols.by_qualified_name.iter().any(|(child_qn, &child_sym)| {
            child_qn.starts_with(&prefix)
                && !child_qn[prefix.len()..].contains('.')   // direct child only
                && matches!(self.kind_of(child_sym), Some(SymbolKind::Entity))
        })
    }

    // ── Query ───────────────────────────────────────────────────

    /// Remove `id` from the `rules_by_functor` index without retracting the
    /// rule. WI-581 doc-fix: `rules_by_functor` is the *enumeration* index (what
    /// [`Self::rules_by_functor`] returns), NOT the SLD goal-resolution index —
    /// that is the *discrimination tree* (queried via `query_view`). The rule is
    /// left in the discrim tree and the KB, reachable by `try_resolve_symbol`
    /// (cite-resolution), `by_domain`, [`Self::live_rule_ids`], and
    /// direct `RuleId` access; SLD candidate selection is unaffected (it already
    /// drops equational heads via its `is_equation` filter in `resolve.rs`,
    /// indexed or not).
    ///
    /// What the unindex actually changes is the `rules_by_functor()` enumeration
    /// — notably `simp_rewrite`'s `[simp]`/`[unfold]` gather
    /// (`has_simp_equations` and the eq-rule walk read `rules_by_functor(eq)`):
    /// after unindexing the cite-only equations, that bucket holds *only* the
    /// indexed `[simp]`/`[unfold]` equations.
    ///
    /// Used for opt-in equational rules per WI-139: equational laws (head is an
    /// `=` / `<=>` application) without a `[simp]` / `[unfold]` attribute are
    /// cite-required only and must not drive automatic `[simp]` rewriting (which
    /// would loop on rules like `add_comm: add(a, b) = add(b, a)`).
    pub fn unindex_functor(&mut self, id: RuleId) {
        let head = self.rule_head(id);
        // WI-812: capture fact-ness before the borrow of `rules_by_functor` — the
        // rule is only unindexed, not retracted, so `is_fact` is still valid.
        let is_fact = self.is_fact(id);
        if let Term::Fn { functor, .. } = *self.terms.get(head) {
            let removed = if let Some(v) = self.rules_by_functor.get_mut(&functor) {
                let before = v.len();
                v.retain(|&rid| rid != id);
                before != v.len()
            } else {
                false
            };
            // WI-812: keep the `has_bodied_rule` gate in step with the bucket. A
            // non-directional equation (the only thing unindexed today, WI-139) is
            // a bodied rule under its `=` / `<=>` head functor, so unindexing it
            // must drop the gate — else `read_facts(eq)` would see a phantom bodied
            // rule. Guarded on `removed` so a later `retract` cannot double-count.
            if removed && !is_fact {
                self.dec_bodied_rule_count(functor);
            }
            // WI-665: defensive. `unindex_functor` is only ever called (WI-139) on
            // NON-directional equations, which the simp gate does NOT count, so this
            // never actually changes THAT gate today — but routing it through the
            // helper keeps the three mutation sites uniform and stays correct if a
            // directional head is ever unindexed. See
            // `invalidate_simp_gate_if_connective`.
            self.invalidate_simp_gate_if_connective(functor);
        }
    }

    /// All active (non-retracted) rule/fact ids with a given top-level functor
    /// symbol — the *enumeration* index (cf. [`Self::unindex_functor`]). SLD goal
    /// resolution does not consult this; it matches via the discrimination tree.
    pub fn rules_by_functor(&self, sym: Symbol) -> Vec<RuleId> {
        self.rules_by_functor
            .get(&sym)
            .map(|v| {
                v.iter()
                    .copied()
                    .filter(|rid| !self.rules[rid.index()].retracted)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Borrowing counterpart of [`Self::rules_by_functor`]: the active (non-retracted)
    /// rule/fact ids with top-level functor `sym`, yielded WITHOUT allocating a `Vec`.
    /// Same filter and order as the owned form. For read-only enumeration that reduces
    /// immediately — `.any()` / `.find()` / `.next()` (first / emptiness) — where it also
    /// SHORT-CIRCUITS. NOT usable when the loop body mutates the KB: the shared borrow
    /// this holds would conflict, so those callers keep the owned `rules_by_functor`.
    pub fn rules_by_functor_iter(&self, sym: Symbol) -> impl Iterator<Item = RuleId> + '_ {
        self.rules_by_functor
            .get(&sym)
            .into_iter()
            .flatten()
            .copied()
            .filter(move |rid| !self.rules[rid.index()].retracted)
    }

    /// Snapshot every active, indexed program clause under `sym`.
    pub fn program_clauses_by_functor(&self, sym: Symbol) -> Vec<ProgramClause> {
        self.rules_by_functor_iter(sym)
            .map(|rid| self.program_clause(rid))
            .collect()
    }

    /// Snapshot every active program clause in `domain`, preserving the
    /// historical `by_domain` enumeration order without exposing `RuleId`.
    pub fn program_clauses_by_domain(&self, domain: Symbol) -> Vec<ProgramClause> {
        self.by_domain(domain)
            .into_iter()
            .map(|rid| self.program_clause(rid))
            .collect()
    }

    /// WI-812: whether `functor` currently has ANY indexed bodied rule (a rule
    /// with a non-empty body). O(1) — a single lookup of the `bodied_rule_counts`
    /// gate maintained at assert / retract / unindex, so [`Self::read_facts`]'s
    /// blanket bodied-rule refusal costs one map read instead of a
    /// `rules_by_functor` bucket scan with a per-row `is_fact`. It separates "is
    /// this functor a pure table?" (this gate) from "which rows match?" (the
    /// discrim query), so the blanket-vs-scoped refusal is a deliberate choice,
    /// not a scan artifact. cf. the cached WI-635 `head_has_vars` / WI-646 simp
    /// gate.
    pub fn has_bodied_rule(&self, functor: Symbol) -> bool {
        self.bodied_rule_counts.get(&functor).is_some_and(|&c| c > 0)
    }

    /// WI-812: one more indexed bodied rule under `functor` — bump the
    /// [`Self::has_bodied_rule`] gate. Called from `push_value_head_entry` beside
    /// the `rules_by_functor` push.
    fn inc_bodied_rule_count(&mut self, functor: Symbol) {
        *self.bodied_rule_counts.entry(functor).or_insert(0) += 1;
    }

    /// WI-812: one fewer indexed bodied rule under `functor` — drop the
    /// [`Self::has_bodied_rule`] gate. Called from `retract` / `unindex_functor`
    /// ONLY when a bodied rule was actually removed from the bucket (the caller's
    /// `removed` guard), so the count never underflows: a present entry is ≥ 1
    /// (zero entries are pruned), and an absent entry is a no-op rather than a
    /// wrapping subtraction.
    fn dec_bodied_rule_count(&mut self, functor: Symbol) {
        if let Some(c) = self.bodied_rule_counts.get_mut(&functor) {
            *c -= 1;
            if *c == 0 {
                self.bodied_rule_counts.remove(&functor);
            }
        }
    }

    /// Every active clause of a given kind, as a WALK over all live clauses —
    /// deliberately NOT an index lookup (see the index-declaration comment for
    /// why no index on `clause_kind` is maintained). Linear in the clause count;
    /// its one production caller runs once per Z3 dispatch, where that cost is
    /// dwarfed by spawning the solver.
    pub fn clauses_of_kind(&self, kind: ClauseKind) -> Vec<RuleId> {
        self.live_rule_ids()
            .into_iter()
            .filter(|&rid| self.rule_clause_kind(rid) == kind)
            .collect()
    }

    /// All active rules/facts belonging to a given domain.
    pub fn by_domain(&self, domain: Symbol) -> Vec<RuleId> {
        self.by_domain
            .get(&domain)
            .map(|v| {
                v.iter()
                    .copied()
                    .filter(|rid| !self.rules[rid.index()].retracted)
                    .collect()
            })
            .unwrap_or_default()
    }


    // ── Rule accessors ───────────────────────────────────────────

    fn program_clause(&self, id: RuleId) -> ProgramClause {
        let rule = &self.rules[id.index()];
        ProgramClause {
            head: rule.head.clone(),
            body_nodes: rule.body_nodes.clone(),
            clause_kind: rule.clause_kind,
            domain: rule.domain,
            meta: rule.meta,
            shared_arity: rule.shared_arity,
        }
    }

    /// Get the head of a rule/fact as a hash-consed `TermId`. The head is stored
    /// carrier-agnostically (`Value`, WI-348 Phase B); the universal case is
    /// `Value::Term`. This is the **single** term-only head reader (WI-348 folded
    /// the former `head_term_id` helper in here — there is no generic "head →
    /// TermId" operation, since a value-fact head has no `TermId`). **Panics on a
    /// value-fact head** (`Value::Entity` / `Value::Node`): the panic is the
    /// deliberate trip-wire — a value fact must never reach a term-only head
    /// reader; carrier-agnostic readers use `rule_head_value` / `TermView`. (The
    /// `is_equation` bug was exactly such a leak, surfaced by this panic, then fixed.)
    ///
    /// WI-663 migrated every reader that **enumerates arbitrary rules** (the
    /// `rules_by_functor` / `by_domain` scans that read a reflect-fact head's
    /// structure — `SortInfo` / `ProofRecord` / `Modifiable` / entity-ctor walks,
    /// and the `[simp]`-equation readers `stored_lhs_functor` / `open_equation`)
    /// onto the graceful `fact_head_term` (skip a value head), matching the WI-659
    /// sort-alias skip. So the surviving callers here are **term-only by
    /// construction** — persistence (the persist API keys on `TermId`, so a value
    /// head cannot enter the store; a *silent* skip there would unsoundly drop a
    /// retrieved fact, hence the loud panic is kept), `unindex_functor` (WI-139
    /// equations), the by-`domain` *bodied-rule* readers (facts, incl. value
    /// facts, are pre-skipped), and heads already gated upstream. A value head
    /// reaching one of those is a genuine kernel-invariant violation the panic
    /// should surface loudly.
    pub fn rule_head(&self, id: RuleId) -> TermId {
        match &self.rules[id.index()].head {
            crate::eval::value::Value::Term { id: t, .. } => *t,
            other => panic!(
                "rule_head: head is not a Term carrier — a value fact reached a \
                 term-only head reader (WI-348); read via `rule_head_value` / \
                 `TermView` instead: {}",
                other.type_name(),
            ),
        }
    }

    /// Get the head of a rule as a carrier-agnostic `Value` (WI-348). The
    /// universal case is `Value::Term`; a value fact (e.g. an `OperationInfo`
    /// carrying a `denoted` effect label) carries a `Value::Entity` / `Value::Node`.
    /// Readers that must tolerate both carriers walk this via `TermView` rather
    /// than calling the panicking `rule_head` term-only reader.
    pub fn rule_head_value(&self, id: RuleId) -> &crate::eval::value::Value {
        &self.rules[id.index()].head
    }

    /// The head of a fact as a ground hash-consed `TermId`, or `None` if it is a
    /// value fact (a `Value::Node`/`Value::Entity`-carrying head — WI-348/WI-366).
    /// The carrier-agnostic skip for the term-only readers of the sort-relation
    /// reflect facts (`SortAlias` / `SortRequiresInfo` / `SortProvidesInfo`): a
    /// value head has no `TermId`, so a term-only reader treats `None` as "skip
    /// this fact" — occurrence-based handling is gated effect-expressions-as-types
    /// work (the producer surfaces a diagnostic). Avoids the `rule_head` panic
    /// on a value head.
    pub fn fact_head_term(&self, id: RuleId) -> Option<TermId> {
        match &self.rules[id.index()].head {
            crate::eval::value::Value::Term { id: t, .. } => Some(*t),
            _ => None,
        }
    }

    /// WI-714 — whether `tid` contains ANY `Var::DeBruijn` (recursively). A rule
    /// head slot that is a bare `DeBruijn` is a free column; a slot that is a
    /// COMPOUND term MENTIONING a DeBruijn (`some(?x)`) cannot be spliced verbatim
    /// into a runnable query goal — its raw DeBruijn would unify reflexively-only
    /// (`kb/resolve.rs` `unify_match_values`) and silently yield zero solutions — so
    /// `build_relation_value` / `relation_clause_columns` reject it loudly. A fully
    /// GROUND compound (`pair(1, 2)`, no DeBruijn) is a legitimate filter and passes.
    pub(crate) fn term_mentions_debruijn(&self, tid: TermId) -> bool {
        match self.get_term(tid) {
            Term::Var(Var::DeBruijn(_)) => true,
            Term::Fn { pos_args, named_args, .. } => {
                let children: SmallVec<[TermId; 8]> = pos_args
                    .iter()
                    .copied()
                    .chain(named_args.iter().map(|(_, a)| *a))
                    .collect();
                children.iter().any(|&a| self.term_mentions_debruijn(a))
            }
            _ => false,
        }
    }

    /// The named args of a fact head when it is a ground `Term::Fn`, else `None`
    /// (a value head, or a non-`Fn` term). An owned clone — the carrier-agnostic
    /// skip peer of [`Self::fact_head_term`] for readers that pull named fields
    /// (`sort_ref` / `spec`) off a sort-relation reflect fact.
    pub fn fact_head_named_args(&self, id: RuleId) -> Option<SmallVec<[(Symbol, TermId); 2]>> {
        match self.get_term(self.fact_head_term(id)?) {
            Term::Fn { named_args, .. } => Some(named_args.clone()),
            _ => None,
        }
    }

    /// Whether a rule id refers to a live (non-retracted) rule. Out-of-bounds
    /// ids return false. Use before reading rule fields when the caller
    /// can't guarantee the id was just produced.
    pub fn is_rule_alive(&self, id: RuleId) -> bool {
        self.rules
            .get(id.index())
            .map(|r| !r.retracted)
            .unwrap_or(false)
    }

    /// Whether a rule is a fact — i.e. has an empty body. Backed by the
    /// occurrence body (`body_nodes`), the sole body representation (WI-246).
    pub fn is_fact(&self, id: RuleId) -> bool {
        self.rules[id.index()].body_nodes.is_empty()
    }

    /// WI-635: whether the stored head carries any `Var::Global` (is non-ground),
    /// read off the cached `head_vars` list set at assert — so the resolver's
    /// fact fast-path gate never walks a (potentially large) head per match. A
    /// var-headed arity-0 fact reads `true` and must NOT take the raw-bind
    /// fast-path — it freshens its head vars per match through `with_fresh_vars`
    /// like any bodyless rule, so two goals matching it bind independently rather
    /// than aliasing the fact's persistent VarIds.
    pub fn rule_head_has_vars(&self, id: RuleId) -> bool {
        !self.rules[id.index()].head_vars.is_empty()
    }

    /// WI-246: the rule body atoms as `NodeOccurrence`s (empty for facts) — the
    /// sole body representation. The form the resolver opens as goals and the
    /// typer / `simp_rewrite` walk.
    pub fn rule_body_nodes(&self, id: RuleId) -> &[Rc<NodeOccurrence>] {
        &self.rules[id.index()].body_nodes
    }

    /// WI-282: replace a rule's body atoms with their typer-rewritten form (the
    /// rule-body peer of [`Self::set_op_body_node`]). Used after dot dispatch rewrites a
    /// body's `Expr::DotApply` to its `Apply`/`field_access` form. Dispatch never
    /// changes a body's variable set (the receiver var is reused, the synthesized
    /// field-name is a `Ref` constant), so the rule's `arity`/`globals`/
    /// `shared_arity` stay valid and the head-indexed discrim entry is untouched.
    pub fn set_rule_body_nodes(&mut self, id: RuleId, body_nodes: Vec<Rc<NodeOccurrence>>) {
        // WI-812: the `has_bodied_rule` gate (`bodied_rule_counts`) tracks
        // body-emptiness ONLY at assert / retract / unindex. This is a 1:1 atom
        // rewrite (dispatch never adds/removes atoms), so fact-ness must not flip —
        // assert it loudly, else a future body-emptiness-changing caller would
        // silently desync the gate.
        debug_assert_eq!(
            self.rules[id.index()].body_nodes.is_empty(),
            body_nodes.is_empty(),
            "set_rule_body_nodes must not flip a rule's fact-ness (WI-812 has_bodied_rule \
             gate is not maintained here)",
        );
        self.rules[id.index()].body_nodes = body_nodes;
    }

    /// Which syntactic form produced this clause — see [`ClauseKind`] (WI-922).
    pub fn rule_clause_kind(&self, id: RuleId) -> ClauseKind {
        self.rules[id.index()].clause_kind
    }

    /// Get the domain of a rule — the enclosing namespace/sort it was
    /// declared in, as a `Symbol`.
    ///
    /// A domain is a NAME, not a term: a rule belongs to exactly one
    /// namespace-or-sort, which the loader always spells as a bare identifier.
    /// It was a `TermId` (a nullary `Term::Fn` wrapping this very symbol) until
    /// every reader — `by_domain`, the requires-guard in `resolve.rs`, the
    /// `[simp]` enclosing-sort guard, `anthill-stl`'s clause reader — unwrapped
    /// it back to the functor through a three-arm `Fn | Ref | Ident` match whose
    /// non-name arms silently `continue`d. The shape was measured across the
    /// whole workspace suite before the change: every domain was a nullary `Fn`,
    /// so the unwrap was total and the fallthrough arms were dead. Carrying the
    /// symbol makes that true by type and deletes the four unwraps.
    pub fn rule_domain(&self, id: RuleId) -> Symbol {
        self.rules[id.index()].domain
    }

    /// The symbol a NAME term denotes — the single `TermId → Symbol` bridge for
    /// the SCOPE/DOMAIN positions, where a term is only ever a bare name
    /// (`make_name_term` / `name_to_sort_term` build exactly a nullary
    /// `Term::Fn`; `Ref`/`Ident` are the same name in the carriers the
    /// parse/reflect sides use).
    ///
    /// Panics on anything else. Every caller holds a term IT built from a name
    /// (`make_name_term` / `name_to_sort_term`), so a non-name is an internal
    /// invariant violation, not bad user input.
    ///
    /// Do NOT reach for this on a term that came from USER SYNTAX. A
    /// `provides Stack[T = Int64] … end` spec lowers to a SortView APPLICATION,
    /// and calling this on it turned valid source into a process abort with no
    /// `path:line:col` — the WI-745 convention for anything a user can trigger is
    /// a `LoadError::Located`. Derive the name from the written name instead
    /// (see `load_provides_block`).
    pub fn name_term_sym(&self, term: TermId) -> Symbol {
        match self.terms.get(term) {
            Term::Fn { functor, pos_args, named_args }
                if pos_args.is_empty() && named_args.is_empty() =>
            {
                *functor
            }
            Term::Ref(s) | Term::Ident(s) => *s,
            other => panic!(
                "name_term_sym: {term:?} is not a name term ({other:?}) — a scope \
                 or domain must be a bare identifier"
            ),
        }
    }

    /// Get the meta of a rule.
    pub fn rule_meta(&self, id: RuleId) -> Option<TermId> {
        self.rules[id.index()].meta
    }

    // ── Fact accessors (aliases for rule accessors) ──────────────

    /// Get the head term of a fact (alias for `rule_head`).
    pub fn fact_term(&self, id: RuleId) -> TermId {
        self.rule_head(id)
    }

    /// Which syntactic form produced this fact (alias for `rule_clause_kind`).
    pub fn fact_clause_kind(&self, id: RuleId) -> ClauseKind {
        self.rule_clause_kind(id)
    }

    /// Get the domain of a fact (alias for `rule_domain`).
    pub fn fact_domain(&self, id: RuleId) -> Symbol {
        self.rule_domain(id)
    }

    /// Get the meta of a fact (alias for `rule_meta`).
    pub fn fact_meta(&self, id: RuleId) -> Option<TermId> {
        self.rule_meta(id)
    }

    // ── Sort management queries ──────────────────────────────────

    /// WI-240 — look up the runtime target op for a spec op dispatched
    /// onto impl sort `impl_sort`. `op_short` is the spec op's short
    /// name symbol (e.g. `lt`). Returns `S.<op>` when the impl
    /// overrides with a runnable body, the spec op itself when it
    /// relies on the spec's rewrite-rule default, or `None` when the
    /// impl carries no entry for `op_short` (the impl doesn't claim to
    /// provide this spec — the typer rejects such dispatches before
    /// this lookup). Direct table read, no string concatenation.
    pub fn sort_ops_lookup(&self, impl_sort: Symbol, op_short: Symbol) -> Option<Symbol> {
        let key = self.canonical_sort_sym(impl_sort);
        self.sort_ops.by_impl.get(&key)?.get(&op_short).copied()
    }

    /// WI-577 — every target op sort `impl_sort` provides in its `sort_ops`
    /// table (the stored `S.<op>` override or inherited spec-op entry). The bulk
    /// face of [`Self::sort_ops_lookup`] (one key), backing `Dictionary.ops`'s
    /// enumeration — which resolves each target through
    /// [`typing::resolve_op_target`], so the raw (possibly placeholder) entry is
    /// what this returns. Empty vec when the impl carries no row; order is
    /// unspecified (a `HashMap` walk) — the enumeration is a set, not a sequence.
    pub fn sort_ops_for_impl(&self, impl_sort: Symbol) -> Vec<Symbol> {
        let key = self.canonical_sort_sym(impl_sort);
        self.sort_ops
            .by_impl
            .get(&key)
            .map(|m| m.values().copied().collect())
            .unwrap_or_default()
    }

    /// WI-240 — record a `(impl_sort, op_short) → target` entry. Called
    /// only by `load::build_sort_ops_table`.
    pub(crate) fn insert_sort_op(&mut self, impl_sort: Symbol, op_short: Symbol, target: Symbol) {
        let key = self.canonical_sort_sym(impl_sort);
        self.sort_ops.by_impl.entry(key).or_default().insert(op_short, target);
    }

    /// WI-616 — record a `value-head functor → carrier's eq` dispatch
    /// entry. Called only by `load::build_eq_dispatch_index`.
    pub(crate) fn insert_eq_dispatch(&mut self, functor: Symbol, target: Symbol) {
        self.sort_ops.eq_dispatch.insert(functor, target);
    }

    /// WI-616 — the carrier `eq` override a value headed by `functor`
    /// dispatches semantic equality through, if any. O(1); `None` = the value's
    /// carrier has no own `eq` (structural equality is its instance).
    pub(crate) fn eq_dispatch_target(&self, functor: Symbol) -> Option<Symbol> {
        self.sort_ops.eq_dispatch.get(&functor).copied()
    }

    /// WI-860 — install the materialized `default_provider` relation (058 §3.6).
    /// Called only by `defaults::build_default_provider_index`.
    pub(crate) fn set_default_provider_index(&mut self, index: defaults::DefaultProviderIndex) {
        self.default_providers = Some(index);
    }

    /// WI-860 — the materialized `default_provider` relation, or `None` on a KB whose
    /// load never built it. Callers must NOT read `None` as "no defaults": the two are
    /// different answers, and 058 rung 2a (WI-861) must fall through to tier 3 on the
    /// first while taking the silent answer on an empty second.
    pub fn default_provider_index(&self) -> Option<&defaults::DefaultProviderIndex> {
        self.default_providers.as_ref()
    }

    /// WI-616 — whether ANY carrier in the KB overrides `eq` (the dispatch
    /// index is non-empty). The resolver's semantic-eq fast path: when no
    /// override exists at all, structurally-distinct operands need no
    /// reachable-override scan.
    pub(crate) fn has_eq_dispatch_entries(&self) -> bool {
        !self.sort_ops.eq_dispatch.is_empty()
    }

    /// Canonicalize any symbol to the single resolved `Symbol` for its
    /// qualified name. The same logical entity (sort, operation, rule head
    /// functor, …) can be interned under several `Symbol`s — e.g. an
    /// unresolved scan-time copy and the resolved load-time copy;
    /// `by_qualified_name` maps the QN to one canonical resolved symbol.
    ///
    /// CAVEAT: this bridges only *same-FQN* copies. A symbol whose
    /// `qualified_name_of` is a *short* name or a *mis-qualified* string has
    /// no `by_qualified_name` entry under that key, so this falls through to
    /// the identity (`unwrap_or(sym)`) and does NOT bridge it to the
    /// canonical copy. Such a divergence must therefore be fixed at the
    /// *producer* (resolve the functor before it is stored/queried), never
    /// papered over by a `canonical_sym` call at the consumer — see WI-581
    /// and the `push_value_head_entry` guardrail.
    pub(crate) fn canonical_sym(&self, sym: Symbol) -> Symbol {
        let qn = self.qualified_name_of(sym);
        self.symbols.by_qualified_name.get(qn).copied().unwrap_or(sym)
    }

    /// Sort-specific alias of [`Self::canonical_sym`]. Used as the `sort_ops`
    /// outer key so a table populated under one copy is found via another at
    /// dispatch. WI-350: also used by the carrier-aware dispatch filter and
    /// the interpreter's value-directed dispatch, which compare sort
    /// identities that may be interned under different copies. WI-581
    /// generalized the body to [`Self::canonical_sym`], since the same
    /// by-QN canonicalization now also serves rule head functors.
    pub(crate) fn canonical_sort_sym(&self, sym: Symbol) -> Symbol {
        self.canonical_sym(sym)
    }

    /// Get sort kind info.
    pub fn sort_kind(&self, sort: Symbol) -> Option<SortKind> {
        self.sort_info.get(&sort).copied()
    }

    /// Iterate sort_info entries (sort name → kind).
    pub fn sort_info_iter(&self) -> impl Iterator<Item = (&Symbol, &SortKind)> {
        self.sort_info.iter()
    }

    /// Get the base substitution for a sort (maps all slots to themselves).
    pub fn sort_base_subst(&self, sym: Symbol) -> Option<&[(Symbol, TermId)]> {
        self.sort_base_subst.get(&sym).map(|v| v.as_slice())
    }

    /// Set the base substitution for a sort.
    pub fn set_sort_base_subst(&mut self, sym: Symbol, subst: Vec<(Symbol, TermId)>) {
        self.sort_base_subst.insert(sym, subst);
    }

    /// Get immediate entity children of a sort.
    pub fn sort_children(&self, sort: Symbol) -> &[Symbol] {
        self.sort_entities
            .get(&sort)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    // ── Counting ─────────────────────────────────────────────────

    /// Number of active (non-retracted) entries with empty body (ground facts).
    pub fn fact_count(&self) -> usize {
        // WI-246: body-emptiness reads the occurrence body (`body_nodes`), not
        // the term `body` — both have equal arity (assert enforces it), so this
        // is unchanged, but it does not depend on the term body that is being
        // retired.
        self.rules.iter().filter(|r| !r.retracted && r.body_nodes.is_empty()).count()
    }

    /// Number of active (non-retracted) entries with non-empty body (proper rules).
    pub fn rule_count(&self) -> usize {
        self.rules.iter().filter(|r| !r.retracted && !r.body_nodes.is_empty()).count()
    }

    /// All live (non-retracted) rule ids — *including* the WI-139 cite-required
    /// equational rules that `unindex_functor` pulled from `rules_by_functor`.
    /// WI-363's op-coverage check enumerates equational definitions this way:
    /// `rule op(args) = rhs` has no functor-index entry, so a `rules_by_functor`
    /// walk would miss it. Returns an owned `Vec` so callers can mutate the KB
    /// (intern, resolve) while iterating.
    pub fn live_rule_ids(&self) -> Vec<RuleId> {
        self.live_rule_ids_iter().collect()
    }

    /// The streaming form of [`Self::live_rule_ids`] — same ids, same order, no Vec.
    /// For a caller that filters down to a handful (WI-898's clause census) and would
    /// otherwise allocate one entry per rule in the KB to discard nearly all of them.
    pub fn live_rule_ids_iter(&self) -> impl Iterator<Item = RuleId> + '_ {
        (0..self.rules.len())
            .map(RuleId::from_index)
            .filter(move |&r| !self.rules[r.index()].retracted)
    }

    /// Live term count in the hash-consed `TermStore`. Diagnostic — used by
    /// 026.1 Q4's acceptance test to verify external-stream scans do not grow
    /// the main term store.
    pub fn term_store_len(&self) -> usize {
        self.terms.len()
    }

    // ── Term matching ─────────────────────────────────────────────
    //
    // match_term inserts `target` into a temporary discrimination tree and
    // queries with `pattern`, reusing the real KB indexing infrastructure.

    /// Match `pattern` against `target` using a temporary discrimination tree.
    ///
    /// Variables on the pattern side bind to corresponding subterms of
    /// `target`. Variables on the target side are inserted into the tree
    /// as variable edges and bind when the pattern provides concrete values.
    ///
    /// Returns `Some(subst)` on success, `None` on failure.
    pub fn match_term(&self, pattern: TermId, target: TermId) -> Option<subst::Substitution> {
        self.match_view(pattern, &term_view::TermIdView(target))
    }

    /// Value-aware match: unifies a rule-head pattern (always `TermId`)
    /// against any [`term_view::TermView`] target. For a `TermIdView(t)` target this
    /// is semantically equivalent to `match_term(pattern, t)`; for a
    /// `Value`-backed target it preserves lineage (no promotion into the
    /// `TermStore`). Variable bindings flow into the result substitution
    /// as `Value::Term` for Term targets and the raw `Value` for others.
    pub fn match_view<V: term_view::TermView>(
        &self,
        pattern: TermId,
        target: &V,
    ) -> Option<subst::Substitution> {
        let mut tree = SubstTree::<()>::new();
        tree.insert_pattern(self, &term_view::TermIdView(pattern), ());
        let results = tree.query_resolved(self, target, |_| pattern);
        results.into_iter()
            .map(|(_, s)| s)
            .find(|s| !s.is_contradiction())
    }

    /// WI-683 — carrier-neutral peer of [`Self::match_view`]: the PATTERN may itself
    /// ride any carrier (a `Value::Node` occurrence / `Value::Entity`), not only
    /// a hash-consed `TermId`. Inserts the pattern via the already-generic
    /// [`SubstTree::insert_pattern`] and resolves the matched leaf against the
    /// pattern's OWN [`term_view::TermView`] (`resolve_leaf_view`), so a
    /// `Value::Node` `forall_impl` antecedent discharges a goal without being
    /// lowered to a term (`reify_goal_value` retired from the assumed-fact path).
    ///
    /// Same match semantics as `match_view` — the resolution (wildcard) query so
    /// a goal's flex-`Global` var binds to the assumed fact's structure, and
    /// `unify_rebind = false` (a `Value::Term` pattern head therefore resolves
    /// byte-identically to `match_view(reify(pattern), target)`, the pre-WI-683
    /// path). `match_view` stays the fast path for the many term-pattern callers
    /// (reflect matching, external rows, simp).
    pub fn match_view_value_pattern<V: term_view::TermView>(
        &self,
        pattern: &crate::eval::value::Value,
        target: &V,
    ) -> Option<subst::Substitution> {
        let mut tree = SubstTree::<()>::new();
        tree.insert_pattern(self, pattern, ());
        let results = tree.query_resolved_value(self, target, false, |_| pattern.clone());
        results.into_iter()
            .map(|(_, s)| s)
            .find(|s| !s.is_contradiction())
    }

    /// One-directional match of a rule-LHS `pattern` against a `target` that may
    /// itself carry flex-`Global` (query) vars — the simp-rewriter's matcher. A
    /// flex-`Global` var on the TARGET side is INERT (matches only a stored
    /// pattern var, never a concrete subterm, and is not self-bound), so the
    /// pattern's vars bind to the target's subterms one-way and a projected
    /// target var rides through unbound (`match(pick(F0,F1), pick(?q,7))` →
    /// `F0↦?q`). This is what `match_view` did WRONG for a var-carrying target
    /// (it ran the resolution wildcard path, which self-binds the target var and
    /// scrambles the match); `match_view` keeps the wildcard behavior for the
    /// assumed-fact / reflect resolution callers, and only the rewriter
    /// (`fire_simp_equation` / the typer) uses this one-directional entry.
    pub fn match_view_oneway<V: term_view::TermView>(
        &self,
        pattern: TermId,
        target: &V,
    ) -> Option<subst::Substitution> {
        let mut tree = SubstTree::<()>::new();
        tree.insert_pattern(self, &term_view::TermIdView(pattern), ());
        let results = tree.query_resolved_mode(self, target, true, |_| pattern);
        results.into_iter()
            .map(|(_, s)| s)
            .find(|s| !s.is_contradiction())
    }

    /// Resolver-only candidate selection, generic over the goal representation:
    /// `pattern` is anything
    /// viewable as a term — `TermIdView(TermId)` for the term-goal path, or a
    /// `Value` / `Value::Node` occurrence goal (WI-246), since the matcher
    /// reads the goal only through [`TermView`] and the discrim tree indexes
    /// rule heads structurally. Avoids lowering an occurrence goal to a
    /// hash-consed term just to look up candidates.
    pub(crate) fn query_view<V: term_view::TermView>(
        &self,
        pattern: &V,
    ) -> Vec<(RuleId, subst::Substitution)> {
        let rules = &self.rules;
        let candidates = self.discrim.query_resolved_value(
            self,
            pattern,
            true,
            |rid: &RuleId| rules[rid.index()].head.clone(),
        );

        let mut results = Vec::new();
        for (rid, tree_subst) in candidates {
            if rules[rid.index()].retracted {
                continue;
            }
            if tree_subst.is_contradiction() {
                continue;
            }
            results.push((rid, tree_subst));
        }
        // Stable-sort: facts (empty body) before rules (non-empty body).
        // The discrimination tree uses HashMap internally, so candidate order
        // is non-deterministic. DFS resolution depends on trying ground facts
        // before recursive rules to find base-case solutions first.
        results.sort_by_key(|(rid, _)| if rules[rid.index()].body_nodes.is_empty() { 0 } else { 1 });
        results
    }

    /// Structurally browse active source clauses whose heads match `pattern`.
    ///
    /// Unlike the resolver's crate-private [`Self::query_view`], this returns
    /// immutable clause snapshots and bindings, never resident `RuleId`s. It is
    /// the public inspection API for tools such as `anthill query --match`.
    /// It is not a fact-read API: callers that need data rows must use
    /// [`Self::read_facts`] or [`Self::read_facts_resolved`].
    pub fn browse_program_clauses_matching<V: term_view::TermView>(
        &self,
        pattern: &V,
    ) -> Vec<ProgramClauseMatch> {
        self.query_view(pattern)
            .into_iter()
            .map(|(rid, bindings)| ProgramClauseMatch {
                clause: self.program_clause(rid),
                bindings,
            })
            .collect()
    }

    /// WI-812: the head `Value`s of resident, non-retracted FACTS whose head
    /// matches `pattern` through the discrimination tree — the indexed peer of a
    /// `rules_by_functor` + `bound_matches` scan, for [`Self::read_facts`]'s
    /// SELECTIVE resident reads (a non-empty `selection` on a functor with a
    /// declared field schema).
    ///
    /// It differs from [`Self::query_view`] in two load-bearing ways, both so the
    /// caller can build the query `pattern` under `&self` without minting fresh
    /// vars:
    /// - it returns head **`Value`s, not `(RuleId, Substitution)`** — keeping the
    ///   `read_facts` read shape `RuleId`-free — and
    /// - it goes through [`SubstTree::query_raw`] and DISCARDS the match
    ///   substitution, taking only the matched leaves, so a query var's binding is
    ///   never folded. `read_facts`'s pattern uses distinct synthetic wildcards
    ///   (`selection_query_pattern`), but this discard is what lets it stay `&self`:
    ///   the wildcard ids need not be freshly minted. `query_view` instead folds the
    ///   substitution through `resolve_leaf`, so a repeated binding would drop the
    ///   row as a spurious `is_contradiction`.
    ///
    /// Only FACT heads are returned (a bodied rule under the functor is dropped
    /// here, not refused — `read_facts` gates the blanket bodied-rule refusal
    /// separately and O(1) via [`Self::has_bodied_rule`], BEFORE calling this).
    /// Retracted leaves are filtered, exactly as `query_view` guards (the discrim
    /// tree may still hold a retracted non-ground head).
    pub(crate) fn query_fact_heads<V: term_view::TermView>(
        &self,
        pattern: &V,
    ) -> Vec<crate::eval::value::Value> {
        self.discrim
            .query_raw(self, pattern)
            .into_iter()
            .filter(|(rid, _)| {
                !self.rules[rid.index()].retracted && self.rules[rid.index()].body_nodes.is_empty()
            })
            .map(|(rid, _)| self.rules[rid.index()].head.clone())
            .collect()
    }

    // ── Variable-aware operations ─────────────────────────────

    /// Collect all VarIds occurring in a term (DFS, deduped).
    pub fn collect_vars(&self, term: TermId) -> Vec<VarId> {
        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        self.collect_vars_rec(term, &mut vars, &mut seen);
        vars
    }

    fn collect_vars_rec(&self, term: TermId, vars: &mut Vec<VarId>, seen: &mut std::collections::HashSet<u32>) {
        match self.terms.get(term) {
            Term::Var(Var::Global(vid)) => {
                if seen.insert(vid.raw()) {
                    vars.push(*vid);
                }
            }
            Term::Var(Var::DeBruijn(_)) => {}
            Term::Fn { pos_args, named_args, .. } => {
                let pos_args = pos_args.clone();
                let named_args = named_args.clone();
                for &id in pos_args.iter() {
                    self.collect_vars_rec(id, vars, seen);
                }
                for &(_, id) in named_args.iter() {
                    self.collect_vars_rec(id, vars, seen);
                }
            }
            _ => {}
        }
    }

    /// Map a function over the children of an Fn term, returning the same TermId
    /// if nothing changed (avoids unnecessary allocation and hash-consing).
    pub(crate) fn map_fn_children(&mut self, term: TermId, mut f: impl FnMut(&mut Self, TermId) -> TermId) -> TermId {
        match self.terms.get(term).clone() {
            Term::Fn { functor, pos_args, named_args } => {
                let mut changed = false;
                let new_pos: SmallVec<[TermId; 4]> = pos_args
                    .iter()
                    .map(|&id| { let r = f(self, id); if r != id { changed = true; } r })
                    .collect();
                let new_named: SmallVec<[(crate::intern::Symbol, TermId); 2]> = named_args
                    .iter()
                    .map(|&(sym, id)| { let r = f(self, id); if r != id { changed = true; } (sym, r) })
                    .collect();
                if changed {
                    self.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named })
                } else {
                    term
                }
            }
            _ => term,
        }
    }

    /// Apply a substitution to a term, replacing Var nodes with their bindings.
    /// Returns a new hash-consed TermId.
    pub fn apply_subst(&mut self, term: TermId, subst: &subst::Substitution) -> TermId {
        match self.terms.get(term).clone() {
            // Term-world substitution: a non-`Term` carrier (a `Value::Node`)
            // can't be a `Term` child, so a var bound to one stays the var.
            Term::Var(Var::Global(vid)) => match subst.resolve_as_value(vid) {
                Some(crate::eval::value::Value::Term { id: t, .. }) => *t,
                _ => term,
            },
            Term::Var(Var::DeBruijn(_)) => term,
            Term::Fn { .. } => self.map_fn_children(term, |kb, id| kb.apply_subst(id, subst)),
            _ => term,
        }
    }

    // ── Walk / reify ──────────────────────────────────────────────

    /// Chase Var→binding→Var chains through a substitution, **term-world**:
    /// returns the final non-variable `TermId`, or the last unbound Var — and a
    /// var bound to a non-`Term` carrier (a `Value::Node`, a scalar) STOPS the
    /// chase at that var (the Node is not represented in the `TermId` result).
    /// Use this only where a `TermId` is genuinely the right shape — building a
    /// term (`apply_subst`), inspecting a synthetic term marker
    /// (`forall_impl` / `push_choice` goal-classification), or recursing over
    /// term structure (`is_ground`, `collect_unbound_vars`). The carrier-faithful
    /// chase that SURFACES a `Value::Node` is [`Self::walk_view`], which the
    /// carrier-neutral builtins read their args through. WI-348.
    pub fn walk(&self, term: TermId, subst: &subst::Substitution) -> TermId {
        use crate::eval::value::Value;
        let mut current = term;
        loop {
            match self.terms.get(current) {
                Term::Var(Var::Global(vid)) => match subst.resolve_as_value(*vid) {
                    Some(Value::Term { id: bound, .. }) => {
                        if *bound == current {
                            return current; // self-referential, stop
                        }
                        current = *bound;
                    }
                    // Non-`Term` carrier (a `Value::Node`/scalar) or unbound:
                    // stop at the var. This is the term-world chase; the
                    // carrier-faithful one is `walk_view`.
                    _ => return current,
                },
                _ => return current,
            }
        }
    }

    /// `TermView`-aware [`Self::walk`] (WI-277): chase Var→binding chains through
    /// the substitution following **both** term and non-term `Value`
    /// bindings, returning the resolved `Value`. `Value::Term(t)` for a
    /// term-shaped result (a `Fn`, a leaf, or an unbound var — to recurse
    /// into / inspect), or a non-term `Value` (`Value::Node`, a literal, …)
    /// when a variable is bound to one. The view-level counterpart of
    /// `walk`, used by the typer-phase rewriter's occurrence build side.
    pub fn walk_view(
        &self,
        term: TermId,
        subst: &subst::Substitution,
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        let mut current = term;
        loop {
            match self.terms.get(current) {
                Term::Var(Var::Global(vid)) => match subst.resolve_as_value(*vid) {
                    Some(Value::Term { id: next, .. }) if *next != current => current = *next,
                    Some(Value::Term { .. }) | None => return Value::term(current),
                    Some(other) => return other.clone(),
                },
                _ => return Value::term(current),
            }
        }
    }

    /// Deep-reify a term through the substitution to a carrier-agnostic
    /// [`crate::eval::Value`] (WI-348). The carrier-faithful successor of the former
    /// `TermId`-only reify: a var bound to a `Value::Node` (a denoted/occurrence
    /// answer) — or any other non-`Term` value — is returned with its
    /// **identity intact**, never materialized to a `TermId` (which is lossy: it
    /// drops the occurrence's identity/span).
    ///
    /// Reification rebuilds **through `Term::Fn` structure**, chasing each var
    /// child's binding chain: an all-`Term` result rebuilds a hash-consed
    /// `Value::Term(Fn)` (the universal case), a `Fn` with any non-`Term` child
    /// becomes the same `Value::Entity` carrier a value fact uses (assembled by
    /// [`Self::fn_value`]). A var bound to a non-`Term` *carrier* (`Value::Node`
    /// / `Entity` / `Tuple` / scalar) is returned **as-is** — its identity is
    /// the answer; recursing into such a carrier's own children to chase a
    /// nested unbound var is unnecessary until value *rule* heads land
    /// (WI-348 Phase C, no consumer yet). Read an answer binding with this; a
    /// caller that handles a non-`Term` carrier narrows explicitly (`if let
    /// Value::Term(t) = …`) or reads it carrier-agnostically via
    /// [`crate::kb::term_view::TermView`], while one that genuinely demands a
    /// hash-consed term uses [`crate::eval::value::Value::expect_term`] (which
    /// fails loud on a non-`Term` carrier — WI-477).
    pub fn reify(&mut self, term: TermId, subst: &subst::Substitution) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        // Chase the var chain carrier-faithfully — `walk_view` surfaces a
        // non-`Term` binding the `TermId`-only `walk` cannot see.
        match self.walk_view(term, subst) {
            Value::Term { id: t, .. } => match self.terms.get(t).clone() {
                Term::Fn { functor, pos_args, named_args } => {
                    let pos: Vec<Value> =
                        pos_args.iter().map(|&id| self.reify(id, subst)).collect();
                    let named: Vec<(Symbol, Value)> = named_args
                        .iter()
                        .map(|&(sym, id)| (sym, self.reify(id, subst)))
                        .collect();
                    self.fn_value(functor, pos, named)
                }
                // Leaf (Const/Ref/Ident/…) or an unbound `Var` — already final.
                _ => Value::term(t),
            },
            // WI-691: a bound non-`Term` carrier. Fully σ-apply it and preserve
            // the carrier — the former `other => other` returned the binding RAW,
            // so a query var bound to a `Node cons(v1, v2)` reified with v1/v2
            // UNRESOLVED even though σ determined them (the WI-690 unfold, which
            // binds a query var to a Node pattern, is the first path to expose
            // this). `reify_value` substitutes a `Node`'s (via
            // `substitute_occurrence`, identity-preserving) / `Entity`'s inner
            // vars, so the answer is fully ground where σ determines it, while a
            // var-free `Node` — e.g. a WI-348 denoted value-in-type binding —
            // rides through with its occurrence identity intact. The carrier is
            // deliberately NOT promoted to a `Term` (that would drop the Node
            // identity `value_fact_full_resolver_search_binds_node_as_value`
            // asserts); an answer stays on the carrier it was proved on.
            other => self.reify_value(&other, subst),
        }
    }

    /// Assemble a functor application `functor(pos…, named…)` from child
    /// `Value`s into its canonical head carrier (WI-348) — the **single source**
    /// of the `Term`-vs-`Value::Entity` decision, shared by [`Self::reify`]
    /// (rebuilding a reified `Fn`) and [`Self::assert_fact_carrier`] (asserting
    /// the result). Children that are all LEAVES rebuild a hash-consed
    /// `Value::Term(Fn)` (the universal case — dedup-able, indexes identically);
    /// any other child forces a `Value::Entity`, which cannot hash-cons but reads
    /// back through `TermView` like its term twin.
    ///
    /// THE TEST IS NOT "IS A `Value::Term`" (WI-1016). A `Value::SymbolRef(s)` is
    /// `Term::Ref(s)` with the interning not yet done — [`Self::alloc_from_value`]
    /// lowers it losslessly, and `TermView` cannot tell the two apart. Reading it
    /// as a non-`Term` child would push the whole application onto the
    /// `Value::Entity` path, and that is not a cosmetic difference:
    /// [`Self::assert_fact_value`] keys an `Entity` head in `value_fact_dedup` (a
    /// `GoalKey`) while a `Term` head keys `fact_dedup` (a `TermId`), and the two
    /// key spaces are DISJOINT — so `f(<sym as SymbolRef>)` and `f(<the same sym
    /// as Term::Ref>)` would store as two facts for one logical fact, and neither
    /// dedup would ever see the other (WI-815).
    ///
    /// THE TEST IS NOW `alloc_from_value`'S OWN LEAF SET (WI-1023), asked through
    /// [`Value::lowers_to_leaf_term`] rather than restated here. The hand-written
    /// `Value::Term | SymbolRef` was narrower by five carriers, and the
    /// disjoint-key-space argument above applies verbatim to every one of them —
    /// `f(Value::Int(1))` took the `Entity` path while `f(1)` built as a term keyed
    /// `fact_dedup`. That was unreachable through `assert_fact_carrier`, whose four
    /// callers all pass `Value::term(..)` children, but NOT through the other caller:
    /// [`Self::reify`] hands this whatever σ bound, so a scalar-bound goal var
    /// reified to a `Value::Entity` twin of a perfectly ordinary ground term.
    ///
    /// WHERE THE SET STOPS IS `LEAF`, not "what lowers" — a `Value::Entity` child
    /// lowers too, and admitting it would (a) make this function's `Err` reachable
    /// (`OverArityConstructor`), demoting a broken-invariant panic to a real failure
    /// mode, and (b) change the carrier of every application with a compound child,
    /// which is a different decision from this one. The three axes are recorded at
    /// the predicate.
    ///
    /// This is the one place a `SymbolRef` is deliberately interned. It is not a
    /// transient: the term it becomes is a CHILD of a hash-consed application that
    /// is about to be asserted or answered, and `Term::Ref` is one node per symbol
    /// — the persistent, heavily-shared structure hash-consing is for.
    fn fn_value(
        &mut self,
        functor: Symbol,
        pos: Vec<crate::eval::value::Value>,
        named: Vec<(Symbol, crate::eval::value::Value)>,
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        // `alloc_from_value` is the one owner of every carrier's lowering (it is
        // where `SymbolRef → Term::Ref` is written); restating its arms here would
        // be a second, untied statement of the variant's whole contract — which is
        // exactly how the old two-arm list drifted. It cannot fail for a child
        // `lowers_to_leaf_term` accepted, so the `Err` is a broken invariant —
        // loud, exactly as the `expect_term` it replaces was.
        let all_lower = pos.iter().all(Value::lowers_to_leaf_term)
            && named.iter().all(|(_, v)| v.lowers_to_leaf_term());
        if all_lower {
            let lower = |kb: &mut Self, v: &Value| {
                kb.alloc_from_value(v)
                    .unwrap_or_else(|e| panic!("fn_value: a leaf child did not lower: {e:?}"))
            };
            let pos_args: SmallVec<[TermId; 4]> =
                pos.iter().map(|v| lower(self, v)).collect();
            let named_args: SmallVec<[(Symbol, TermId); 2]> = named
                .iter()
                .map(|(s, v)| (*s, lower(self, v)))
                .collect();
            Value::term(self.alloc(Term::Fn { functor, pos_args, named_args }))
        } else {
            Value::Entity {
                functor,
                pos: std::rc::Rc::from(pos),
                named: std::rc::Rc::from(named),
            }
        }
    }

    /// Deep-reify a goal [`crate::eval::Value`] through `σ`, carrier-faithfully — the
    /// `Value`-carrier front for [`Self::reify`] (WI-348). A `Value::Term`
    /// deep-substitutes via `reify` (rebuilding through `Term::Fn`); a
    /// `Value::Node` occurrence substitutes via `substitute_occurrence`, which
    /// **preserves the occurrence's identity/span** — it is spliced/rewritten in
    /// place, never rebuilt structurally and never dropped to a bare var; a
    /// scalar / value-level var passes through. Used at the resolver's goal
    /// boundaries that need a σ-applied goal as a `Value` — NAF sub-resolution
    /// and assumed-fact matching — so neither lowers an occurrence goal to a
    /// hash-consed term. It was distinct from `reify_goal_value` (resolve.rs),
    /// the term-only materializer (`Value -> TermId`, no `σ`) — that one is now
    /// DELETED, its last readers having turned out to be reads the view answers,
    /// so this is the only `Value`-in / `Value`-out σ-applier left.
    ///
    /// WI-535: `pub` so the host reflect bridge (`anthill-stl`) realizes its
    /// carrier-faithful `Substitution.apply` / `KB.apply_core_subst` over a
    /// `Value`-carried `Term` through this — an occurrence-carried goal keeps
    /// its identity/span instead of being reified to a bare `TermId`.
    pub fn reify_value(
        &mut self,
        v: &crate::eval::value::Value,
        subst: &subst::Substitution,
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        match v {
            Value::Term { id: t, .. } => self.reify(*t, subst),
            Value::Node(occ) => {
                Value::Node(node_occurrence::substitute_occurrence(self, occ, subst))
            }
            // WI-547: a BOUND bare value-level var resolves to its binding
            // (recursively, so a `z → w → …` chain collapses even when σ is not
            // path-compressed) — applying σ means substituting the vars it binds.
            // An UNBOUND var still passes through (the resolver goal boundaries
            // rely on a free value-level var staying free), as does a
            // Rigid/DeBruijn var (not a σ-bound logical var). The term-internal
            // case is already handled by `reify` above. Uses `resolve_as_value`
            // (parent-chain aware, like `reify`/`walk_view`), and guards the
            // degenerate self-binding `vid ↦ vid` — which `compose` can synthesize
            // (`{z↦w} ∘ {w↦z}`) — against unbounded recursion, mirroring the
            // self-binding short-circuit in `walk_view`/`reify`/`occurs_in_value`.
            Value::Var(var) => match var.as_global() {
                Some(vid) => match subst.resolve_as_value(vid) {
                    None => v.clone(),
                    Some(Value::Var(v2)) if v2.as_global() == Some(vid) => v.clone(),
                    Some(bound) => {
                        let bound = bound.clone();
                        self.reify_value(&bound, subst)
                    }
                },
                None => v.clone(),
            },
            // WI-629: a COMPOUND value carrier — a `Value::Entity` (the `not`/`or`
            // wrapper `make_goal_value` synthesizes) or a `Value::Tuple` (only ever
            // a nested child value) — must reify its CHILDREN: applying σ means
            // substituting the vars bound anywhere inside. Without these arms it fell
            // to `other.clone()` and passed through unchanged, so a `not(Entity{…})`
            // NAF inner reified with unbound vars still inside; the sub-resolution
            // (which starts from an EMPTY σ — [`SearchStream::step_naf`] line
            // ~1709) then floundered even after a sibling goal had bound them,
            // making the deep-groundness gate (which reads σ) and the reification
            // disagree.
            Value::Entity { functor, pos, named } => {
                let (pos, named) = self.reify_value_children(pos, named, subst);
                Value::Entity { functor: *functor, pos, named }
            }
            Value::Tuple { pos, named } => {
                let (pos, named) = self.reify_value_children(pos, named, subst);
                Value::Tuple { pos, named }
            }
            other => other.clone(),
        }
    }

    /// WI-629: reify (fully σ-apply) the positional + named children of a compound
    /// value carrier (`Value::Entity`/`Tuple`). The child slices borrow from the
    /// caller's `&Value`, not from `self`, so the `&mut self` [`Self::reify_value`]
    /// recursion iterates them directly; named args keep their symbol keys.
    fn reify_value_children(
        &mut self,
        pos: &Rc<[crate::eval::value::Value]>,
        named: &Rc<[(Symbol, crate::eval::value::Value)]>,
        subst: &subst::Substitution,
    ) -> (Rc<[crate::eval::value::Value]>, Rc<[(Symbol, crate::eval::value::Value)]>) {
        use crate::eval::value::Value;
        let mut new_pos: Vec<Value> = Vec::with_capacity(pos.len());
        for c in pos.iter() {
            new_pos.push(self.reify_value(c, subst));
        }
        let mut new_named: Vec<(Symbol, Value)> = Vec::with_capacity(named.len());
        for (s, c) in named.iter() {
            new_named.push((*s, self.reify_value(c, subst)));
        }
        (Rc::from(new_pos), Rc::from(new_named))
    }

    // ── De Bruijn conversion ────────────────────────────────────

    /// Assert a rule with De Bruijn conversion applied, occurrence body supplied
    /// directly (WI-246/WI-372 — the single rule-DeBruijn-assertion path). The
    /// loader builds the occurrences natively from the parse IR; the synthesized
    /// / hand-built callers convert a term body once via
    /// [`Self::term_body_to_nodes`]. The `head` is carrier-agnostic (WI-373):
    /// every existing caller passes a `TermId` (→ `Value::Term`), but it may also
    /// carry a `Value::Node`/`Entity` value head whose vars close to De Bruijn
    /// like a term head's (an `Expr` Node child works; a *denoted* `Type` Node
    /// child still needs the WI-342-P3 Type-occurrence var-walk). The rule's free
    /// vars are collected from the head + occurrence body in the same
    /// first-occurrence order (`collect_value_head_vars` mirrors
    /// `collect_occurrence_global_vars_ordered` mirrors `collect_vars_rec`), then
    /// `finalize_rule_debruijn_nodes` closes head + occurrences.
    pub fn assert_rule_debruijn_with_nodes(
        &mut self,
        head: impl Into<crate::eval::value::Value>,
        body_nodes: Vec<Rc<NodeOccurrence>>,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        let head = head.into();
        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        self.collect_value_head_vars(&head, &mut vars, &mut seen);
        for n in &body_nodes {
            node_occurrence::collect_occurrence_global_vars_ordered(self, n, &mut vars, &mut seen);
        }
        self.finalize_rule_debruijn_nodes(head, body_nodes, vars, 0, clause_kind, domain, meta)
    }

    /// WI-635: collect a stored fact/rule head's `Var::Global`s carrier-agnostically
    /// for the `RuleEntry.head_vars` cache — first-occurrence order, deduped via
    /// `seen`. Read by the resolver's fact fast-path gate (`rule_head_has_vars`)
    /// and by `with_fresh_vars`' arity-0 legacy path (which seeds its rename set
    /// from the cache, so the head is never walked per match).
    ///
    /// A `Value::Term` walks via `collect_vars_rec` (the WI-635 population: user
    /// facts whose omitted entity fields the loader fills with fresh Globals). A
    /// `Value::Entity`/`Tuple` head (a value-fact carrier) recurses its children,
    /// so a value fact's Term child — e.g. an `OperationInfo`'s `type_params`
    /// cons-list of Globals — is covered. A `Value::Node` (denoted value-in-type)
    /// is LENIENTLY skipped: its type/effect occurrence cannot be walked without
    /// the type-field kb-threading migration that
    /// `collect_occurrence_global_vars_ordered` still asserts on. That is sound
    /// here — unlike `collect_value_head_vars`, which MUST count every var so the
    /// De Bruijn arity is exact (hence its assert), this cache only drives
    /// freshening/gating, so a missed occurrence var degrades to the pre-WI-635
    /// fast-path behavior for that one var, never a wrong arity. Denoted places
    /// are concrete sort refs in practice (no Globals to miss); widen this to walk
    /// the occurrence once that migration lands.
    fn collect_head_global_vars(
        &self,
        head: &crate::eval::value::Value,
        vars: &mut Vec<VarId>,
        seen: &mut std::collections::HashSet<u32>,
    ) {
        use crate::eval::value::Value;
        match head {
            Value::Term { id: t, .. } => self.collect_vars_rec(*t, vars, seen),
            Value::Entity { pos, named, .. } | Value::Tuple { pos, named, .. } => {
                for c in pos.iter() {
                    self.collect_head_global_vars(c, vars, seen);
                }
                for (_, c) in named.iter() {
                    self.collect_head_global_vars(c, vars, seen);
                }
            }
            // Denoted value-in-type: leniently skipped (see the doc comment).
            // Deliberate, not a fall-through.
            Value::Node(_) => {}
            // Scalar leaves (Int/Str/Bool/Unit/…) and any runtime carrier carry no
            // Global head var.
            _ => {}
        }
    }

    /// Collect a rule head's Global `VarId`s in first-occurrence order,
    /// carrier-agnostically (WI-373) — the head twin of
    /// `collect_occurrence_global_vars_ordered` (body). A `Value::Term` walks via
    /// `collect_vars_rec`; a `Value::Node` via the occurrence walker; a
    /// `Value::Entity` recurses pos-then-named, matching the term-head walk order
    /// so head/body De Bruijn indices align.
    pub(crate) fn collect_value_head_vars(
        &self,
        head: &crate::eval::value::Value,
        vars: &mut Vec<VarId>,
        seen: &mut std::collections::HashSet<u32>,
    ) {
        use crate::eval::value::Value;
        match head {
            Value::Term { id: t, .. } => self.collect_vars_rec(*t, vars, seen),
            Value::Node(occ) => {
                node_occurrence::collect_occurrence_global_vars_ordered(self, occ, vars, seen)
            }
            // A functor head or an anonymous tuple: recurse into the children
            // (any of which can carry vars), pos before named.
            Value::Entity { pos, named, .. } | Value::Tuple { pos, named, .. } => {
                for c in pos.iter() {
                    self.collect_value_head_vars(c, vars, seen);
                }
                for (_, c) in named.iter() {
                    self.collect_value_head_vars(c, vars, seen);
                }
            }
            // Scalar head children carry no Global vars.
            Value::Int(_) | Value::BigInt(_) | Value::Float(_) | Value::Bool(_)
            | Value::Str(_) | Value::Unit => {}
            // A bare value-level var (WI-109) or a runtime carrier
            // (Closure/Stream/…) is not a shape a stored rule head takes —
            // fail loudly rather than silently undercount the rule's arity.
            other => debug_assert!(
                false,
                "WI-373: unexpected value rule-head carrier in var-collection: {}",
                other.type_name(),
            ),
        }
    }

    /// Close a rule head's Global vars to De Bruijn, carrier-agnostically
    /// (WI-373) — the head twin of the body's `node_to_debruijn` close, kept in
    /// lockstep with [`Self::collect_value_head_vars`] (same carriers, same
    /// recursion). A `Value::Term` closes via `term_to_debruijn`; a `Value::Node`
    /// occurrence via `node_to_debruijn`; a `Value::Entity`/`Tuple` recurses into
    /// its children; a scalar has no vars; any other carrier fails loudly.
    fn close_value_head_debruijn(
        &mut self,
        head: crate::eval::value::Value,
        vars: &[VarId],
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        match head {
            Value::Term { id: t, .. } => Value::term(self.term_to_debruijn(t, vars)),
            Value::Node(occ) => Value::Node(node_occurrence::node_to_debruijn(self, &occ, vars)),
            Value::Entity { functor, pos, named, .. } => {
                let pos: Vec<Value> = pos
                    .iter()
                    .map(|c| self.close_value_head_debruijn(c.clone(), vars))
                    .collect();
                let named: Vec<(Symbol, Value)> = named
                    .iter()
                    .map(|(s, c)| (*s, self.close_value_head_debruijn(c.clone(), vars)))
                    .collect();
                Value::Entity { functor, pos: std::rc::Rc::from(pos), named: std::rc::Rc::from(named) }
            }
            Value::Tuple { pos, named, .. } => {
                let pos: Vec<Value> = pos
                    .iter()
                    .map(|c| self.close_value_head_debruijn(c.clone(), vars))
                    .collect();
                let named: Vec<(Symbol, Value)> = named
                    .iter()
                    .map(|(s, c)| (*s, self.close_value_head_debruijn(c.clone(), vars)))
                    .collect();
                Value::Tuple { pos: std::rc::Rc::from(pos), named: std::rc::Rc::from(named) }
            }
            // Scalars have no vars to close.
            h @ (Value::Int(_) | Value::BigInt(_) | Value::Float(_) | Value::Bool(_)
            | Value::Str(_) | Value::Unit) => h,
            // A bare value-level var or a runtime carrier is not a stored
            // rule-head shape — fail loudly rather than leave a var unclosed.
            h => {
                debug_assert!(
                    false,
                    "WI-373: unexpected value rule-head carrier in De Bruijn close: {}",
                    h.type_name(),
                );
                h
            }
        }
    }

    /// WI-246/WI-372 finalize: the occurrence body is supplied directly (a term
    /// body is materialized first via [`Self::term_body_to_nodes`]). Closes head
    /// + occurrence body to the shared De Bruijn form against `vars` (collected
    /// by the caller from head + occurrences, in first-occurrence order), inserts
    /// via `assert_rule_nodes`, and records arity / shared_arity / globals. The
    /// single rule-DeBruijn-closure path (`assert_rule_debruijn_with_nodes` and
    /// its shared-frame twin both land here).
    #[allow(clippy::too_many_arguments)]
    fn finalize_rule_debruijn_nodes(
        &mut self,
        head: impl Into<crate::eval::value::Value>,
        body_nodes: Vec<Rc<NodeOccurrence>>,
        vars: Vec<VarId>,
        shared_arity: u32,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        let head = head.into();
        let arity = vars.len() as u32;
        // Close head + occurrence body to De Bruijn against the shared `vars`
        // (Global → DeBruijn, including vars inside any TermId pattern/param
        // fields the occurrence carries); ground facts (`vars` empty) keep both
        // as-is. The head close is carrier-agnostic (`close_value_head_debruijn`),
        // mirroring the body's `node_to_debruijn`.
        let (db_head, db_nodes) = if vars.is_empty() {
            (head, body_nodes)
        } else {
            let new_head = self.close_value_head_debruijn(head, &vars);
            let mut out = Vec::with_capacity(body_nodes.len());
            for n in &body_nodes {
                out.push(node_occurrence::node_to_debruijn(self, n, &vars));
            }
            (new_head, out)
        };
        let rule_id = self.assert_rule_nodes(db_head, db_nodes, clause_kind, domain, meta);
        let entry = &mut self.rules[rule_id.index()];
        entry.arity = arity;
        entry.shared_arity = shared_arity;
        entry.globals = vars;
        rule_id
    }

    /// Pre-DeBruijn Global VarIds for this rule, indexed by their
    /// assigned DeBruijn number. Empty for ground facts. Used by
    /// structured-proof step synthesis (proposal 031) to align step
    /// rule variables with the parent's frame.
    pub fn rule_globals(&self, id: RuleId) -> &[VarId] {
        &self.rules[id.index()].globals
    }

    /// WI-582 — install typed rule-pattern bounds on an already-asserted rule.
    /// Each `(var, bound)` names a HEAD variable (a pre-DeBruijn Global VarId,
    /// as collected by the loader from a `?x: T` annotation) and the type its
    /// eventual binding must conform to. The variable is mapped to its DeBruijn
    /// index via `globals` (set by `finalize_rule_debruijn_nodes`), so the stored
    /// bound is keyed by index — stable across rule firing, where the index
    /// opens to a fresh VarId. A variable absent from `globals` is a loader bug
    /// (a typed annotation on a non-head variable); flag it loudly rather than
    /// silently dropping the bound.
    ///
    /// `pub(crate)`, not `pub` (WI-903): the loader's refusal is what keeps a bound
    /// off a rule no site enforces it on, so the installer must not be reachable
    /// around it from outside the crate.
    pub(crate) fn install_rule_type_bounds(&mut self, id: RuleId, var_bounds: &[(VarId, TermId)]) {
        let globals = self.rules[id.index()].globals.clone();
        let mut bounds: Vec<(u32, TermId)> = Vec::with_capacity(var_bounds.len());
        for &(vid, bound) in var_bounds {
            match globals.iter().position(|&g| g == vid) {
                // The DeBruijn index is `len - 1 - position` (innermost-is-0), the
                // SAME reversal `term_to_debruijn` / `node_to_debruijn` apply when
                // closing the head. Storing the raw position would key the firing
                // check (`typed_pattern_bounds_hold`, which indexes the opened
                // globals `fresh[db_index]`) to the WRONG variable for any rule
                // with >= 2 vars.
                Some(idx) => bounds.push(((globals.len() - 1 - idx) as u32, bound)),
                None => debug_assert!(
                    false,
                    "WI-582: typed-pattern variable {vid:?} is not a head variable of rule {id:?}"
                ),
            }
        }
        self.rules[id.index()].type_bounds = bounds;
    }

    /// WI-582 — the typed rule-pattern bounds for `id`: `(debruijn_index,
    /// bound_type)` pairs the firing check reads. Empty for untyped rules.
    pub fn rule_type_bounds(&self, id: RuleId) -> &[(u32, TermId)] {
        &self.rules[id.index()].type_bounds
    }

    /// Resolve a qualified rule name to the first matching `RuleId`.
    /// Convenience for the common pattern of looking up a rule's
    /// metadata (globals, shared_arity, ...) by name. For labeled
    /// multi-head rules see [`Self::rule_ids_by_qn`] — they have
    /// multiple rids sharing one label.
    pub fn rule_id_by_qn(&self, qn: &str) -> Option<RuleId> {
        let sym = self.try_resolve_symbol(qn)?;
        if let Some(ids) = self.rules_by_label.get(&sym) {
            if let Some(&rid) = ids.first() {
                return Some(rid);
            }
        }
        self.rules_by_functor_iter(sym).next()
    }

    /// All rule ids that resolve to `qn` — label-first, then
    /// rules_by_functor fallback. Labeled multi-head rules
    /// (`rule X: H1, H2 :- B`) desugar at load time into N rules
    /// sharing label X; `using X` fans out over this list so each
    /// head contributes its own lifted implication clause. For
    /// unlabeled `qn` the returned ids are the rules whose head's
    /// functor symbol resolves to `qn` (SLD lookup semantics).
    pub fn rule_ids_by_qn(&self, qn: &str) -> Vec<RuleId> {
        self.try_resolve_symbol(qn).map(|sym| self.clause_ids_of(sym)).unwrap_or_default()
    }

    /// The SYMBOL-keyed body of [`Self::rule_ids_by_qn`] — label-first, then the
    /// head-functor fallback. Split out (WI-898) so the "which clauses does this
    /// name have?" question has ONE owner: [`Self::has_clauses_under`] asks it as a
    /// predicate, and a caller holding a `Symbol` no longer has to round-trip
    /// through the qualified-name string to reach the same answer.
    pub fn clause_ids_of(&self, sym: Symbol) -> Vec<RuleId> {
        if let Some(ids) = self.rules_by_label.get(&sym) {
            if !ids.is_empty() {
                return ids.clone();
            }
        }
        self.rules_by_functor(sym)
    }

    /// WI-898 — does `sym` OWN CLAUSES? The allocation-free predicate form of
    /// [`Self::clause_ids_of`], asked where only existence matters.
    pub fn has_clauses_under(&self, sym: Symbol) -> bool {
        self.rules_by_label.get(&sym).is_some_and(|ids| !ids.is_empty())
            || self.rules_by_functor_iter(sym).next().is_some()
    }

    /// WI-898 — DOES `sym` DENOTE A RELATION? The single question behind every
    /// WI-714 citation position (bare, applied, as an argument, and eval's two
    /// twins), replacing the `matches!(kind, Goal | Rule)` each of them used to
    /// spell for itself.
    ///
    /// IT IS DERIVED, NOT STAMPED, and that is the point. A relation is a name with
    /// CLAUSES INDEXED UNDER IT — that is what makes `relation_columns_across_clauses`
    /// able to answer. `Goal`/`Rule` are the kinds a clause-owning head earns, so
    /// they pass directly. An `EquationFunctor` normally owns none (its clauses sit
    /// under the `eq`/`unify` connective) and so does NOT pass — the WI-898 fix. But a
    /// scope may write one name in BOTH head shapes, and then a predicate clause IS
    /// indexed under it and the relational reading is real; asking the index says so
    /// whatever the mint stamped.
    ///
    /// Deriving replaced a stamp-then-patch first cut, which classified such a name by
    /// which of its two rules pass 3 reached first — MEASURED: the same two rules
    /// swapped answered `EquationFunctor` and `Goal`. Patching that needed a mutable
    /// kind, and a mutable kind is a fact two writers can disagree about; there is no
    /// stamp here to disagree with. The extra index read costs nothing on the common
    /// paths: only an `EquationFunctor` reaches it.
    pub fn cites_a_relation(&self, sym: Symbol) -> bool {
        use crate::intern::SymbolKind;
        // `has_kind`, not `kind_of`: this is the MEMBERSHIP question WI-925 split the
        // two readings for. `kind_of` reports the keyword the declaration opened with,
        // so asking it "is this a relation" would re-create the source-order dependence
        // — the same defect, one level up, that made this function derived rather than
        // stamped in the first place.
        self.has_kind(sym, SymbolKind::Goal)
            || self.has_kind(sym, SymbolKind::Rule)
            || (self.has_kind(sym, SymbolKind::EquationFunctor) && self.has_clauses_under(sym))
    }

    /// Snapshot every active source clause resolved by `qn`: labeled clauses
    /// first, then the head-functor fallback. This is the value-facing peer of
    /// [`Self::rule_ids_by_qn`] for program inspection outside the resolver.
    pub fn program_clauses_by_qn(&self, qn: &str) -> Vec<ProgramClause> {
        self.rule_ids_by_qn(qn)
            .into_iter()
            .filter(|rid| self.is_rule_alive(*rid))
            .map(|rid| self.program_clause(rid))
            .collect()
    }

    /// Citation handle for labeled rules. `None` for unlabeled rules
    /// (those resolve via `rules_by_functor` on the head).
    pub fn rule_label(&self, id: RuleId) -> Option<Symbol> {
        self.rules[id.index()].label
    }

    /// Tag an already-asserted rule with a citation label so
    /// `rule_id_by_qn(label_qn)` resolves it even when the head's
    /// functor differs from the label (post-proposal-032 unified
    /// head-as-conclusion encoding). Idempotent re-tagging with the
    /// same label is allowed; a different label is a programming bug
    /// and panics.
    pub fn set_rule_label(&mut self, id: RuleId, label: Symbol) {
        let entry = &mut self.rules[id.index()];
        match entry.label {
            Some(existing) if existing == label => return,
            Some(existing) => panic!(
                "rule {id:?} already labeled {existing:?}, cannot re-tag as {label:?}"),
            None => entry.label = Some(label),
        }
        self.rules_by_label.entry(label).or_default().push(id);
    }

    /// Assert a rule using a CALLER-PROVIDED Global VarIds list as the DeBruijn
    /// frame (proposal 031), occurrence body supplied directly (WI-372). The
    /// head + occurrences are reindexed against the collected `vars` rather than
    /// recomputed from the rule's own free vars; any Global VarId NOT in
    /// `seed_globals` is appended in first-seen order. Used by
    /// `dispatch_structured` to synthesize step rules in the parent's variable
    /// frame so shared variable names produce identical DeBruijn indices (and
    /// therefore identical `var_<i>` SMT names) across the parent rule and every
    /// step's cited-rule lift. The shared-frame twin of
    /// [`Self::assert_rule_debruijn_with_nodes`]; a term-bodied caller converts
    /// once via [`Self::term_body_to_nodes`].
    pub fn assert_rule_debruijn_with_nodes_in_frame(
        &mut self,
        head: impl Into<crate::eval::value::Value>,
        body_nodes: Vec<Rc<NodeOccurrence>>,
        seed_globals: &[VarId],
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> RuleId {
        // `term_to_debruijn` / `node_to_debruijn` map positions in reverse (last
        // entry → DeBruijn 0). Parent's seed must stay at the TAIL so its shared
        // vars retain DeBruijn 0..seed_len-1 (matching the parent's own
        // assignment); step-introduced vars are prepended. Vars are collected
        // from head + occurrences in the SAME first-occurrence order as
        // `assert_rule_debruijn_with_nodes` (so frame alignment is preserved).
        let head = head.into();
        let seen: std::collections::HashSet<u32> =
            seed_globals.iter().map(|v| v.raw()).collect();
        let mut vars = Vec::new();
        let mut collected = std::collections::HashSet::new();
        self.collect_value_head_vars(&head, &mut vars, &mut collected);
        for n in &body_nodes {
            node_occurrence::collect_occurrence_global_vars_ordered(self, n, &mut vars, &mut collected);
        }
        vars.retain(|v| !seen.contains(&v.raw()));
        vars.extend(seed_globals.iter().copied());

        let shared_arity = seed_globals.len() as u32;
        self.finalize_rule_debruijn_nodes(head, body_nodes, vars, shared_arity, clause_kind, domain, meta)
    }

    /// Number of leading DeBruijn slots that are shared with a parent
    /// rule's frame. Zero for ordinary rules; positive for
    /// step rules synthesized via `assert_rule_debruijn_with_nodes_in_frame`.
    pub fn rule_shared_arity(&self, id: RuleId) -> u32 {
        self.rules[id.index()].shared_arity
    }

    /// Convert a single term: replace Global(vid) with DeBruijn(index).
    /// Index is `var_order.len() - 1 - position_in_var_order`.
    fn term_to_debruijn(&mut self, term: TermId, var_order: &[VarId]) -> TermId {
        match self.terms.get(term).clone() {
            Term::Var(Var::Global(vid)) => {
                if let Some(pos) = var_order.iter().position(|v| *v == vid) {
                    let idx = (var_order.len() - 1 - pos) as u32;
                    self.alloc(Term::Var(Var::DeBruijn(idx)))
                } else {
                    term // not in var_order, keep as Global
                }
            }
            Term::Var(Var::DeBruijn(_)) => term,
            Term::Fn { .. } => self.map_fn_children(term, |kb, id| kb.term_to_debruijn(id, var_order)),
            _ => term,
        }
    }

    /// Open a de Bruijn term: replace `DeBruijn(i)` with `Global(fresh_vars[i])`.
    /// `fresh_vars`: array of fresh VarIds, indexed by de Bruijn index.
    pub fn term_from_debruijn(&mut self, term: TermId, fresh_vars: &[VarId]) -> TermId {
        match self.terms.get(term).clone() {
            Term::Var(Var::DeBruijn(idx)) => {
                if let Some(&vid) = fresh_vars.get(idx as usize) {
                    self.alloc(Term::Var(Var::Global(vid)))
                } else {
                    term // index out of range, keep as DeBruijn
                }
            }
            Term::Var(Var::Global(_)) => term,
            Term::Fn { .. } => self.map_fn_children(term, |kb, id| kb.term_from_debruijn(id, fresh_vars)),
            _ => term,
        }
    }

    /// Get the arity (number of de Bruijn variables) of a rule.
    pub fn rule_arity(&self, id: RuleId) -> u32 {
        self.rules[id.index()].arity
    }

    // ── Rule classification ─────────────────────────────────────

    /// The canonical equality functor — `anthill.prelude.PartialEq.eq`, the head
    /// symbol every loaded equation (`lhs = rhs`) carries, and the one the loader
    /// builds equation heads with (`load.rs`).
    ///
    /// `[simp]` firing (`simp_rewrite`) must look up `rules_by_functor` under
    /// *this* symbol, not a freshly-interned bare `eq`: the two differ once the
    /// prelude is registered, so a bare `intern("eq")` finds none of the loaded
    /// `[simp]` equations (WI-283).
    ///
    /// WI-969 — PANICS on a KB that was never bootstrapped, where this used to
    /// fall back to a bare `intern("eq")`. The fallback had no production
    /// reachability (every real path loads, and every load calls
    /// [`load::register_prelude`]); it existed
    /// so unit tests could skip bootstrap, and it bought that at the price of a
    /// SECOND spelling of the canonical equality head. That second spelling fails
    /// silently in the worst way — a `[simp]` rule built on it simply never
    /// matches, so the rewrite does not happen and nothing reports why (WI-283 is
    /// that bug). A missing prelude is now a loud, immediate error instead.
    pub fn eq_functor(&mut self) -> Symbol {
        // WI-644 / proposal 004: the `eq`/`neq` ops moved from `Eq` to its base
        // `PartialEq` (Eq is now the lawful marker requiring PartialEq). Equation
        // heads and `[simp]` lookups key on this symbol.
        self.try_resolve_symbol("anthill.prelude.PartialEq.eq").expect(
            "eq_functor: `anthill.prelude.PartialEq.eq` is unregistered — this KB was \
             never bootstrapped. Load into it (every load entry point bootstraps) or, \
             for a hand-built KB that never loads, call `load::register_prelude` first.",
        )
    }

    /// The canonical unification functor — `anthill.kernel.unify`, the head an
    /// `<=>`-spelled equation carries (proposal 049). The bind-side peer of
    /// [`Self::eq_functor`]: equational rule selection (`apply_eq_rules`, the
    /// typer's `try_fire`) queries/scans under BOTH so a migrated `<=>` equation
    /// and a legacy `=` one are both found while WI-526's `=`→`<=>` relabel is
    /// in flight.
    ///
    /// WI-969 — PANICS on a never-bootstrapped KB, for the reasons at
    /// [`Self::eq_functor`]; the bare-`unify` fallback is gone.
    pub fn unify_functor(&mut self) -> Symbol {
        self.try_resolve_symbol("anthill.kernel.unify").expect(
            "unify_functor: `anthill.kernel.unify` is unregistered — this KB was never \
             bootstrapped. Load into it (every load entry point bootstraps) or, for a \
             hand-built KB that never loads, call `load::register_prelude` first.",
        )
    }

    /// WI-627: is `functor` the KB's canonical equality / unification connective
    /// head — the `anthill.prelude.PartialEq.eq` (`=`) or `anthill.kernel.unify` (`<=>`)
    /// symbol every genuine equation carries? Compares RESOLVED SYMBOL IDENTITY,
    /// not the short name: a carrier's OWN `eq` operation (`Set.eq` / `Map.eq` —
    /// the WI-350/WI-444 short-name override the semantic `=`/`eq` dispatch
    /// resolves against) is a DIFFERENT symbol that merely *shares* the short
    /// name, so it is a normal relational op — NOT an equational law to be
    /// unindexed by WI-139 nor dropped from SLD candidates by [`Self::is_equation`].
    /// This is the single source of truth `is_equation` (here) and
    /// [`load::is_equational_head`](crate::kb::load::is_equational_head) both
    /// classify through, so the two can never diverge.
    ///
    /// Reads the cached [`Self::eq_connective_sym`] / [`Self::unify_connective_sym`]
    /// (O(1), no interning — the `&self`-only peer of the `&mut`
    /// [`Self::eq_functor`] / [`Self::unify_functor`]). Each connective is tested
    /// INDEPENDENTLY, by EXACT SYMBOL, so the classification never hinges on both
    /// being defined together.
    ///
    /// WI-969 — an uncached connective answers `false`: a KB with no canonical
    /// equality connective has no equality connective. It used to fall back to
    /// SHORT-NAME matching, which is precisely the `Map.eq` / `Set.eq`
    /// mis-classification WI-627 fixed — a carrier's own `eq` merely SHARES the
    /// short name and is a normal relational op, so matching it here would unindex
    /// it (WI-139) and drop it from SLD candidates. [`Self::cache_connective_syms`]
    /// already documented that arm as the hazard to avoid; now it cannot be taken.
    /// Only a never-bootstrapped KB reaches this branch (the cache is filled by
    /// `register_builtin_tags` and `resolve_builtins`), and `false` is a
    /// DEFINED answer there rather than a guess — the same line the sibling
    /// fallbacks in `eq_functor` / `unify_functor` were removed on.
    pub(crate) fn is_equality_connective_functor(&self, functor: Symbol) -> bool {
        // Two `Symbol` comparisons, always — an uncached connective is `None`, which
        // no `Some(functor)` equals. WI-969: this was a closure over a short name
        // because the uncached case did string work; nothing here reads a name now.
        self.eq_connective_sym == Some(functor) || self.unify_connective_sym == Some(functor)
    }

    /// WI-665: drop the cached simp gate ([`Self::simp_gate_cache`]) only when a
    /// mutation touched the `eq`/`unify` buckets — the ONLY functors
    /// [`super::resolve`]'s `has_directional_rewrite` counts (it scans
    /// `simp_equation_rids`, i.e. those two buckets). A mutation to any other
    /// functor cannot change the gate's value, so leaving the cache intact is
    /// sound and avoids the recompute WI-646 forced on every fact write. The
    /// gate-dependency predicate is exactly [`Self::is_equality_connective_functor`]
    /// — the same one `has_directional_rewrite` classifies through — so the
    /// invalidation can never under-match the computation (the WI-643 stale-gate
    /// class). O(1): the connective syms are cached, so this is two `Symbol`
    /// compares on the common prelude-loaded path.
    fn invalidate_simp_gate_if_connective(&mut self, functor: Symbol) {
        if self.is_equality_connective_functor(functor) {
            self.simp_gate_cache = None;
        }
    }

    /// WI-627: (re)resolve and cache the equality-connective symbols read by
    /// [`Self::is_equality_connective_functor`]. Called at the end of
    /// [`Self::register_builtin_tags`] (where `register_builtin_tag` first defines
    /// both) and [`Self::resolve_builtins`] (the builtin-symbol remap hook), so the
    /// cache reflects the final canonical symbols regardless of load order.
    fn cache_connective_syms(&mut self) {
        // WI-644 split: the `eq` op lives on `PartialEq` (Eq is the lawful marker
        // requiring it), so the canonical `=` connective a genuine equation head
        // carries is `PartialEq.eq` (== `eq_functor()`), NOT the pre-split `Eq.eq`.
        // Keying on `Eq.eq` here would resolve to `None`, and the `is_equality_-
        // connective_functor` fallback would revert to SHORT-NAME matching — exactly
        // the mis-classification of a carrier's own `eq` (`Map.eq`/`Set.eq`) that
        // WI-627 fixed.
        self.eq_connective_sym = self.try_resolve_symbol("anthill.prelude.PartialEq.eq");
        self.unify_connective_sym = self.try_resolve_symbol("anthill.kernel.unify");
    }

    /// WI-646 — the candidate equational rule ids for `[simp]`/`[unfold]` firing:
    /// the `eq` (`=`) bucket plus the `unify` (`<=>`) bucket. ONE helper for the eq+unify
    /// SELECTION that `has_simp_equations`, `try_fire`, `fire_simp_equation` (and
    /// the [`Self::has_directional_rewrite`] gate) all previously spelled inline —
    /// so the gate can never again drift from the fire sites (that drift, an
    /// `eq`-only gate against `eq`+`unify` fire sites, is exactly what caused the
    /// WI-643 regression). Callers still apply their own per-rule filter
    /// (`is_equation` + `[simp]` / directional) on the returned ids.
    pub(crate) fn simp_equation_rids(&mut self) -> Vec<RuleId> {
        let eq_sym = self.eq_functor();
        let unify_sym = self.unify_functor();
        let mut rids = self.rules_by_functor(eq_sym);
        if unify_sym != eq_sym {
            rids.extend(self.rules_by_functor(unify_sym));
        }
        rids
    }

    /// Check if a rule is an equation: head functor is the canonical `eq` (`=`)
    /// or `unify` (`<=>`, proposal 049) connective with 2 positional args and an
    /// empty body. The classification is **type-independent** — purely the head
    /// shape — so it recognizes a migrated `<=>` equation identically to a legacy
    /// `=` one. WI-627: the connective test is by RESOLVED SYMBOL
    /// ([`Self::is_equality_connective_functor`]), so a carrier's own bodyless
    /// `eq(empty(), empty())` base case (`Map.eq`, a different symbol sharing the
    /// short name) is NOT mistaken for a law and dropped from SLD candidates.
    pub fn is_equation(&self, id: RuleId) -> bool {
        let entry = &self.rules[id.index()];
        if !entry.body_nodes.is_empty() || entry.retracted {
            return false;
        }
        // WI-348: the resolver's candidate triage (`resolve.rs` eq/non-eq split)
        // calls this on EVERY matched candidate, so a value-fact head — a
        // `Modify[c]`-effect `OperationInfo`, an entity `FieldInfo`, a
        // value-in-type fact — reaches here and must NOT hit the term-only
        // `rule_head` reader (which panics on a `Value::Entity`/`Value::Node`).
        // Read the head functor + positional arity carrier-agnostically via
        // `TermView`: behaviour-identical for the universal `Value::Term(Fn)` head
        // (same functor symbol, `pos_arity == pos_args.len()`), and a value fact —
        // never `eq`-headed — falls through to `false` as it always should.
        match term_view::TermView::head(&entry.head, self) {
            term_view::ViewHead::Functor { functor: Some(functor), pos_arity, .. } => {
                self.is_equality_connective_functor(functor) && pos_arity == 2
            }
            _ => false,
        }
    }

    /// Instantiate a rule's body with fresh variables, incorporating bindings
    /// from a discrimination tree match.
    ///
    /// The discrim tree's `tree_subst` has a mix of entries:
    /// - **Query vars** → rule-head subterms (concrete values or `Var(rule_vid)`)
    /// - **Rule vars** → concrete query subterms (when query had concrete values)
    ///
    /// This method:
    /// 1. Builds a rename map: for each rule var, use concrete value from
    ///    tree_subst if available, otherwise create a fresh var
    /// 2. Applies rename to rule body → `fresh_body`
    /// 3. Builds `answer_links` mapping query vars to fresh vars (or concrete
    ///    values) based on tree_subst entries
    ///
    /// Returns `(fresh_nodes, answer_links)`: the opened, head-match-renamed
    /// occurrence body (pushed by the resolver as `Value::Node` goals) and
    /// `answer_links` mapping query variables to their fresh counterparts (or
    /// concrete values).
    pub fn with_fresh_vars(
        &mut self,
        id: RuleId,
        tree_subst: &subst::Substitution,
    ) -> (Vec<Rc<NodeOccurrence>>, subst::Substitution) {
        let arity = self.rules[id.index()].arity;
        // WI-373 gap 3 (delivered): a query var matched against a position
        // INSIDE a value rule head now threads a nested `VarPath` and
        // `extract_value_at_path` descends into the head's `Value::Node` child
        // (the discrim binding-extraction), so the head match enters
        // `tree_subst` carrier-faithfully — no longer an empty/unconstrained
        // answer. The arity > 0 path below never reads the head term (the
        // match is fully encoded in `tree_subst`), so a value rule head no
        // longer needs the term-only `rule_head` reader here. Only the
        // arity == 0 legacy path reads it (for the head's Global vars) — it
        // takes `rule_head` locally, and a value head there stays the LOUD
        // guard (a ground value-headed rule has no head vars to collect; an
        // arity-0 value rule with head vars is WI-342-P3 / gap 1 territory).
        // WI-246: the rule's occurrence body — opened + head-match-renamed, then
        // pushed by the resolver as `Value::Node` goals (and driving the
        // caller-var delay pre-check). The term body (`RuleEntry.body`) is no
        // longer opened/renamed here — it is on no resolution path.
        let body_nodes = self.rules[id.index()].body_nodes.clone();

        // WI-246 / WI-636: matching a value goal binds head/rule vars to
        // non-`Term` subparts of the goal. Every De Bruijn / rename / answer-link
        // walk below reads `tree_subst` term-only (`iter_terms` in the arity > 0
        // passes; `resolve_as_value` narrowed to `Value::Term` in the arity-0
        // legacy path), so a non-`Term` entry left as a `Value` is SILENTLY
        // dropped — losing the head-match constraint and letting the body run
        // unconstrained (a wrong under-bound answer, or exponential
        // over-exploration). Concretely (WI-636): a synthetic `u32::MAX - n` entry
        // bound to a non-`Term` value never enters `body_rename`, and a non-`Term`
        // query-var link never reaches `answer_links`.
        //
        // So route EVERY non-`Term` carrier through the total `value_to_term`
        // boundary here, at this single choke point (it precedes the arity split,
        // so it hardens both paths):
        //  - Reify the structural subset to a hash-consed term — `Node` losslessly
        //    via `occurrence_to_term`, an `Entity` (recursing through its
        //    children), and the scalar / `Var` leaves — so the walks below see it.
        //    A `Value::Entity{ctor, [scalar…]}` operand (the common eq-bridge
        //    case) now fires the rule correctly instead of being dropped.
        //  - A carrier with NO faithful term form — an opaque runtime handle
        //    (`Closure`/`Stream`/`Map`/`Cell`/`Substitution`/`Requirement`), a
        //    term-less `Unit`/`Tuple`, or an `Entity` carrying one — cannot enter
        //    the TermId `body_rename` machinery, so the rule candidate simply can't
        //    fire over this match: DROP it (mark `contradiction`, exactly like the
        //    occurs-check drop below and the resolver's `tree_subst`-contradiction
        //    drop). This IS reachable on real input — the WI-625 eval→SLD
        //    `eq`/`neq` bridge feeds raw ground operands (`Value::Entity{ctor,
        //    [Value::Tuple…]}`) into a rule-backed `eq`'s head match — so a
        //    process-aborting panic here would crash on legitimate user code.
        //    Dropping the candidate makes `eq` fall back to its structural verdict
        //    (what it already does when no override can decide), not a silent
        //    unbound-var wrong answer. Reifying the operand at the producer (the
        //    eq-bridge) is the deeper fix — recorded against WI-625.
        // Fast-path: an all-`Term` `tree_subst` (every stdlib case today) passes
        // through untouched (no rebuild, preserves any parent chain).
        let normalized;
        let tree_subst = if tree_subst
            .iter()
            .any(|(_, v)| !matches!(v, crate::eval::value::Value::Term { .. }))
        {
            let entries: Vec<(VarId, crate::eval::value::Value)> =
                tree_subst.iter().map(|(v, val)| (*v, val.clone())).collect();
            let mut norm = subst::Substitution::new();
            for (vid, val) in entries {
                match val {
                    crate::eval::value::Value::Term { id: t, .. } => norm.bind(self, vid, t),
                    other => match node_occurrence::value_to_term(self, &other) {
                        Ok(t) => norm.bind(self, vid, t),
                        // Un-reifiable carrier (Tuple / opaque handle / Unit, or an
                        // Entity carrying one): can't ride the TermId body_rename,
                        // so this candidate can't match — drop it gracefully.
                        Err(_e) => {
                            let mut contradicted = subst::Substitution::new();
                            contradicted.contradiction = true;
                            return (Vec::new(), contradicted);
                        }
                    },
                }
            }
            normalized = norm;
            &normalized
        } else {
            tree_subst
        };

        if arity > 0 {
            // De Bruijn path: allocate N fresh vars, open DeBruijn to Global
            let name_sym = self.intern("_");
            let fresh_vars: Vec<VarId> = (0..arity)
                .map(|_| self.fresh_var(name_sym))
                .collect();

            // Build answer_links (query var → fresh var) and body_rename
            // (fresh var → concrete value from head match).
            //
            // tree_subst contains two kinds of entries:
            // 1. Synthetic VarId(u32::MAX - n): DeBruijn var n matched a
            //    concrete query value. These are substituted directly into
            //    the body via body_rename. NOT added to answer_links — the
            //    fresh var is eliminated from the body, so adding it to the
            //    caller's substitution via bind_compressed would be dead
            //    work (O(n²) scan for nothing).
            // 2. Query VarId: query var matched a subterm of the rule head.
            //    Open any DeBruijn vars in the value to their fresh globals.
            let mut answer_links = subst::Substitution::new();
            let mut body_rename = subst::Substitution::new();
            // Walk only Value::Term bindings — this code path uses TermIds
            // for DeBruijn rename + caller-var linkage. Non-Term bindings
            // from external streams flow through a different path.
            //
            // Two passes (WI-624): `body_rename` must be COMPLETE before any
            // query-var link is opened. A nonlinear head (`unbox(box(v: ?v), ?v)`)
            // binds the rule var concretely through one occurrence (a synthetic
            // entry) while a query var links to the SAME rule var through
            // another; the link must resolve through `body_rename`, else it
            // dangles on a fresh var the rename-substituted body never binds
            // and the answer leaks an unbound fresh var. (The arity-0 legacy
            // path below always threaded links through its `rename` — this
            // restores that parity for the De Bruijn path.)
            for (ts_vid, bound_term) in tree_subst.iter_terms() {
                // `u32::MAX - n` decode (`Var::synthetic_debruijn_index`); this
                // is now its sole caller (the former `apply_eq_rules` /
                // `instantiate_eq_rhs` site is gone — `fire_simp_equation` binds
                // head vars via `match_view` instead).
                if let Some(db_index) = Var::synthetic_debruijn_index(ts_vid, arity) {
                    if let Some(&fresh_vid) = fresh_vars.get(db_index) {
                        body_rename.bind(self, fresh_vid, bound_term);
                    }
                }
            }
            for (ts_vid, bound_term) in tree_subst.iter_terms() {
                if Var::synthetic_debruijn_index(ts_vid, arity).is_some() {
                    continue;
                }
                let opened = self.term_from_debruijn(bound_term, &fresh_vars);
                let linked = if body_rename.is_empty() {
                    opened
                } else {
                    let linked = self.apply_subst(opened, &body_rename);
                    // Occurs check: the rename can route the query var's own
                    // term back into its link (`p(box(v: g(?q)), ?q)` links
                    // ?q → g(?q)); the SLD bind path is not occurs-checked and
                    // a cyclic σ overflows reify/fingerprint. Correct
                    // semantics is occurs-FAILURE — flag the whole match as
                    // contradictory (the resolver drops the candidate, same as
                    // a tree_subst contradiction). Resolving through the links
                    // built so far also catches mutual cycles
                    // (?a → f(?b), ?b → g(?a)). Pure opened links can't cycle
                    // (a rule head has no query vars), so the check rides the
                    // rename branch only.
                    if self.occurs_in_value(
                        ts_vid,
                        &crate::eval::value::Value::term(linked),
                        &answer_links,
                    ) {
                        answer_links.contradiction = true;
                        break;
                    }
                    linked
                };
                answer_links.bind(self, ts_vid, linked);
            }

            // Occurrence body: De Bruijn-open with the same fresh vars, then
            // apply the head-match rename via `substitute_occurrence` (replace
            // fresh vars with the concrete head-match values; unmatched fresh
            // vars stay as variables, bound during body resolution).
            // WI-298: thread `self` into the opener so it can remap DeBruijn
            // vars inside the remaining TermId-typed Expr fields
            // (Let.type_annotation, Apply.type_args, ApplyWithin.type_args)
            // via `term_from_debruijn`, mirroring `node_to_debruijn` on the
            // closing side.
            let mut opened_nodes: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(body_nodes.len());
            for n in body_nodes.iter() {
                opened_nodes.push(node_occurrence::open_debruijn_node(self, n, &fresh_vars));
            }
            let final_nodes = if body_rename.bindings.is_empty() {
                opened_nodes
            } else {
                let mut out = Vec::with_capacity(opened_nodes.len());
                for n in &opened_nodes {
                    out.push(node_occurrence::substitute_occurrence(self, n, &body_rename));
                }
                out
            };

            (final_nodes, answer_links)
        } else {
            // Legacy path: Global vars (ground facts or rules not yet converted).
            // WI-635: the head's Global vars were collected carrier-agnostically
            // at assert (`head_vars`), so here we neither re-walk the head per
            // match (the workitem fact set is large) nor read the term-only
            // `rule_head`. Dropping that read makes this path carrier-neutral: a
            // value (`Node`/`Entity`) head no longer panics reaching here, and its
            // Globals (e.g. an `OperationInfo`'s `type_params` cons-list) freshen
            // like any other — closing the value-fact half of the same alias
            // hazard. Seed the rename set from the cache, then add the occurrence
            // body's own Globals (empty for a fact; legacy bodies use Global vars,
            // parallel to `body_nodes`).
            let mut all_vars = self.rules[id.index()].head_vars.clone();
            let mut seen: std::collections::HashSet<u32> =
                all_vars.iter().map(|v| v.raw()).collect();
            for n in &body_nodes {
                node_occurrence::collect_occurrence_global_vars(n, &mut all_vars, &mut seen);
            }

            let mut rename = subst::Substitution::new();
            for vid in &all_vars {
                // Term-narrow is safe here: the top-of-function normalization
                // (WI-636) already reified every non-`Term` binding to a term (or
                // dropped the whole candidate on an un-reifiable carrier), so
                // `resolve_as_value` sees a `Value::Term` for any bound rule var —
                // a `Node`/scalar/`Entity` no longer falls through to a fresh var
                // and drops its head-match constraint.
                if let Some(crate::eval::value::Value::Term { id: bound, .. }) =
                    tree_subst.resolve_as_value(*vid)
                {
                    let bound = *bound;
                    if !matches!(self.terms.get(bound), Term::Var(_)) {
                        rename.bind(self, *vid, bound);
                        continue;
                    }
                }
                let fresh = self.fresh_var(vid.name());
                let fresh_term = self.alloc(Term::Var(Var::Global(fresh)));
                rename.bind(self, *vid, fresh_term);
            }

            // Occurrence body: legacy bodies already use Global vars, so just
            // apply the same `rename` via `substitute_occurrence`.
            let mut final_nodes = Vec::with_capacity(body_nodes.len());
            for n in &body_nodes {
                final_nodes.push(node_occurrence::substitute_occurrence(self, n, &rename));
            }

            let mut answer_links = subst::Substitution::new();
            for (ts_vid, bound_term) in tree_subst.iter_terms() {
                if all_vars.contains(&ts_vid) {
                    continue;
                }
                match self.terms.get(bound_term) {
                    Term::Var(Var::Global(rule_vid)) => {
                        let rule_vid = *rule_vid;
                        if let Some(crate::eval::value::Value::Term { id: renamed, .. }) =
                            rename.resolve_as_value(rule_vid)
                        {
                            answer_links.bind(self, ts_vid, *renamed);
                        }
                    }
                    _ => {
                        let renamed_term = self.apply_subst(bound_term, &rename);
                        answer_links.bind(self, ts_vid, renamed_term);
                    }
                }
            }

            (final_nodes, answer_links)
        }
    }

    // ── Helpers ─────────────────────────────────────────────────

    /// Convenience: allocate a nullary functor term (name with no args).
    /// WI-511: routes through [`Self::alloc`], so a constructor symbol
    /// canonicalizes to `Ref(c)` (a sort / non-constructor name stays `Fn`).
    pub fn make_name_term(&mut self, name: &str) -> TermId {
        let sym = self.symbols.intern(name);
        self.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// Look up a qualified name and create a nullary Fn term.
    /// Falls back to intern() if no resolved symbol exists.
    /// Callers should pass qualified names (e.g. "Color.red", not "red").
    pub fn resolve_qualified_name_term(&mut self, name: &str) -> TermId {
        let sym = self.resolve_qualified_name_sym(name);
        // `self.terms.alloc`, NOT `self.alloc` / `make_name_term_from_sym`:
        // this must yield the literal nullary `Term::Fn`, and `KnowledgeBase::
        // alloc` rewrites one to `Term::Ref` when the symbol is a CONSTRUCTOR
        // (WI-511). Callers here ask for a NAME term and read the functor back
        // off it, so routing through the canonicalizer hands them a `Ref` for
        // `Color.red` and breaks the read.
        self.terms.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// The symbol behind [`Self::resolve_qualified_name_term`] — resolved by
    /// qualified name, or interned if this KB has never seen it. Wanted
    /// directly wherever a name is used as a KEY rather than as a term: a
    /// rule's `domain`, a `by_domain` lookup.
    pub fn resolve_qualified_name_sym(&mut self, name: &str) -> Symbol {
        match self.symbols.by_qualified_name.get(name) {
            Some(&found) => found,
            None => self.symbols.intern(name),
        }
    }

    /// Look up a resolved symbol by qualified name or short name.
    ///
    /// Panics if no resolved symbol is found — all functor names must be
    /// pre-defined in register_prelude() or scan_definitions().
    pub fn resolve_symbol(&self, name: &str) -> Symbol {
        if let Some(found) = self.try_resolve_symbol(name) {
            return found;
        }
        panic!(
            "resolve_symbol: '{}' is not a resolved symbol. \
             Define it in register_prelude() or ensure it is scanned.",
            name
        );
    }

    /// Look up an already-interned symbol by its exact name without
    /// allocating a new one. Unlike `try_resolve_symbol`, this matches
    /// the raw intern key (e.g. a bare op short name like `lt`), not a
    /// qualified name. Returns `None` when the name was never interned.
    /// WI-240 — used by the eval's dispatch table lookup to recover the
    /// short-name symbol `build_sort_ops_table` keyed its entries by.
    pub fn lookup_symbol(&self, name: &str) -> Option<Symbol> {
        self.symbols.lookup(name)
    }

    /// Look up a resolved symbol by qualified name.
    pub fn try_resolve_symbol(&self, name: &str) -> Option<Symbol> {
        self.symbols.by_qualified_name.get(name).copied()
    }

    /// THE NAME LADDER AT `_global` — what a HOST-supplied name (an extent owner's
    /// functor, a [`FactRef`](crate::kb::extent::FactRef)'s owner) denotes. The same
    /// question every other position asks, so the same function
    /// (`load::resolve_name_in_kb`) with `_global` as the scope; spelling it
    /// separately is how a mount comes to take a functor its author never named (WI-908).
    ///
    /// A SHORT name therefore resolves only if it is IN SCOPE or in the IMPLICIT TIER
    /// (`load::resolve_implicit` — `SortInfo`, `cons`, …, which is short-name keyed and
    /// still answers here). The absolute rung is dotted-only, per WI-476.
    pub fn resolve_name_in_global(&mut self, name: &str) -> ResolveResult {
        let global = self.global_scope();
        crate::kb::load::resolve_name_in_kb(self, name, global)
    }

    /// Check if a qualified name has a defined symbol in the symbol table.
    pub fn has_qualified_name(&self, name: &str) -> bool {
        self.symbols.by_qualified_name.contains_key(name)
    }

    /// Resolve a qualified name and return its short name (if defined).
    pub fn qualified_short_name(&self, name: &str) -> Option<&str> {
        self.symbols.by_qualified_name.get(name).map(|&sym| self.symbols.local_name(sym))
    }

    /// Allocate a nullary functor term from an already-interned symbol.
    /// WI-511: routes through [`Self::alloc`], so a constructor symbol
    /// canonicalizes to `Ref(c)` (a sort / non-constructor name stays `Fn`).
    pub fn make_name_term_from_sym(&mut self, sym: Symbol) -> TermId {
        self.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// Allocate an entity `Term::Fn`, canonicalizing its named args to the
    /// functor's declared field order via [`Self::canonicalize_record_named_args`]. This
    /// is the single funnel for Rust-side entity-term construction (WI-299):
    /// the discrimination matcher (`discrim.rs`) descends named keys
    /// *positionally* and the loader canonicalizes loaded patterns/facts to
    /// declared field order (`load.rs` via `entity_field_names`), so a built
    /// term MUST use that same order or it silently matches zero solutions.
    /// Builders route through here instead of sorting named args ad-hoc by
    /// `Symbol::index()` (interning order), which only *coincidentally* equals
    /// declared order and would break under any change to interning order, with
    /// no error. `pos_args` pass through unchanged (positional order is already
    /// significant). When the functor has no registered field list,
    /// `canonicalize_record_named_args` falls back to interning order — preserving the
    /// prior behavior for anonymous shapes.
    pub fn make_entity_term(
        &mut self,
        functor: Symbol,
        pos_args: SmallVec<[TermId; 4]>,
        mut named_args: SmallVec<[(Symbol, TermId); 2]>,
    ) -> TermId {
        self.canonicalize_record_named_args(functor, &mut named_args);
        self.alloc(Term::Fn { functor, pos_args, named_args })
    }

    // ── List construction ────────────────────────────────────────

    /// Build a cons-list term from a slice of TermIds — `cons(head:, tail:)` over a
    /// nullary `nil`, the shape every `List[T]` in the term carrier takes.
    ///
    /// THE SINGLE OWNER of the STRICT policy — resolve the prelude `List`
    /// constructors, panicking if they are absent. Three more copies of this loop
    /// existed (`load::build_list`, `load::build_cons_list`,
    /// `node_occurrence::build_list_termid` — the last one's own doc calling itself a
    /// "mirror of `load.rs::build_list`"), and a shape with four constructors is one
    /// edit away from four shapes. Only the symbol POLICY genuinely varied, so that is
    /// all that is left: this function and `term_ser::build_cons_list` (which falls
    /// back to a bare `intern` for a schema-less deserialize) each pick their symbols
    /// and hand the spine to [`Self::build_list_with`].
    ///
    /// The three merged copies allocated `Fn{cons, [(head, x), (tail, acc)]}` RAW,
    /// while the spine goes through [`Self::make_entity_term`] and so canonicalizes
    /// the pair first. That step is a no-op — `cons`'s declared field order IS
    /// `head, tail` — but it is the no-op that cannot rot: a schema-less `cons` falls
    /// back to INTERNING order, and the raw form would then disagree with every rule
    /// pattern the loader built through the canonicalizing path. The `debug_assert`
    /// below is what makes "no-op" a measurement rather than a claim: it stayed silent
    /// across the whole suite, and was verified to FIRE when inverted, so the merge is
    /// byte-preserving and any future reorder is loud.
    ///
    /// A nullary `nil` allocs as the bare `Ref(nil)` via [`Self::alloc`]'s WI-511
    /// canon, which is what lets a built list match a pattern spelled with a bare
    /// `nil` (WI-436) — the reason the occurrence-side `build_occurrence_cons_list`
    /// deliberately does NOT share this code: it follows the bare-pattern convention
    /// on purpose.
    pub fn build_list(&mut self, items: &[TermId]) -> TermId {
        let nil_sym = self.resolve_symbol("anthill.prelude.List.nil");
        let cons_sym = self.resolve_symbol("anthill.prelude.List.cons");
        debug_assert!(
            {
                let (h, t) = (self.intern("head"), self.intern("tail"));
                let mut probe = [(h, ()), (t, ())];
                self.canonicalize_record_named_args(cons_sym, &mut probe);
                probe.iter().map(|(s, _)| *s).eq([h, t])
            },
            "cons(head, tail) must already be canonical — the raw-alloc list builders \
             merged into this function relied on it, so a reorder here means the merge \
             changed stored bytes",
        );
        self.build_list_with(nil_sym, cons_sym, items)
    }

    /// The cons/nil spine, over CALLER-SUPPLIED constructors — the one loop behind
    /// both list-building policies (see [`Self::build_list`] for which they are and
    /// why only the symbol lookup differs).
    ///
    /// Named args go through [`Self::make_entity_term`], so a `cons` with a registered
    /// schema stores its pair in DECLARED order and a schema-less one in interning
    /// order — the same rule every other record builder follows, rather than a
    /// hand-rolled order that only happens to agree.
    pub(crate) fn build_list_with(
        &mut self,
        nil_sym: Symbol,
        cons_sym: Symbol,
        items: &[TermId],
    ) -> TermId {
        let head_sym = self.intern("head");
        let tail_sym = self.intern("tail");
        let mut list = self.alloc(Term::Fn {
            functor: nil_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        for &item in items.iter().rev() {
            let mut args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            args.push((head_sym, item));
            args.push((tail_sym, list));
            list = self.make_entity_term(cons_sym, SmallVec::new(), args);
        }
        list
    }

    /// WI-537 / WI-067 / WI-552: the canonical binder-reference reflect-term twin
    /// `var_ref(name: Ref(sym))` (head `Functor{anthill.reflect.Expr.var_ref}`).
    /// The SINGLE home of this shape — `occurrence_to_term`'s `VarRef` arm and the
    /// load-time `wrap_places_as_var_ref` (clause / guarded-effect parameter
    /// occurrences, WI-552) both call here, so the canonical form (which migrated
    /// Ident→Opaque→var_ref across WI-537) has exactly one constructor
    /// (`binder_ref_value` mints the matching `Value::Node` twin). WI-552 retired
    /// the discharge-side normalize pass: a binder is now emitted as `var_ref` at
    /// the producer, not re-typed from a bare `Ref` at the consumer.
    pub fn make_var_ref_term(&mut self, name: Symbol) -> TermId {
        let var_ref = self.resolve_symbol("anthill.reflect.Expr.var_ref");
        let name_ref = self.alloc(Term::Ref(name));
        let k_name = self.intern("name");
        self.alloc(Term::Fn {
            functor: var_ref,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(k_name, name_ref)]),
        })
    }

    // ── Type term constructors (anthill.prelude.Type entities) ───

    /// `sort_ref(name: <sym>)` — reference to a named sort.
    pub fn make_sort_ref(&mut self, sort_sym: Symbol) -> TermId {
        // WI-361 producer flip: a bare sort is the term `Ref(S)` itself — no
        // `sort_ref(name: Ref(S))` wrapper. The sort symbol IS the functor for
        // discrimination (`rules_by_functor`, discrim top-edge); dual-form readers
        // (`extract_sort_ref_sym` / `type_head`) still recognize the deep
        // `sort_ref` shape for any residual/reflect terms.
        self.alloc(Term::Ref(sort_sym))
    }

    // ── WI-342: Value-carried (occurrence) type builders ───────────────
    //
    // Peers of the `make_*` `TermId` builders above, producing the
    // `Value`-carried form (`Rc<NodeOccurrence>` with `NodeKind::Type` /
    // `NodeKind::EffectExpr`) required once a subtree carries a real `denoted`
    // occurrence (the carrier rule, design doc §2). These do NOT allocate in
    // the `TermStore` — they wrap occurrences — and are NOT yet called from the
    // live loader (dual-path; the `TermId` builders stay the live path until
    // P3 routes `unify_types` onto `TermView`). Ground children ride in
    // `TypeChild::Ground(TermId)`; only the `denoted` spine is occurrence-linked.

    /// `denoted(value: NodeOccurrence)` carried as a Type occurrence
    /// (`TypeNode::Denoted`). `value` is the carried source content — for
    /// `Modify[c]` an `Expr::Ref(c)` occurrence (see [`Self::make_denoted_occ_ref`]).
    /// The SOLE `denoted` builder: every production value-in-type rides as this
    /// `Value::Node` occurrence (WI-366 retired the ground `TermId` `denoted`).
    pub fn make_denoted_occ(
        &self,
        value: Rc<NodeOccurrence>,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_type(node_occurrence::TypeNode::Denoted { value }, span, owner)
    }

    /// Convenience: `denoted(value: Ref(sym))` carried as an occurrence — the
    /// occurrence-form peer of `make_denoted(alloc(Term::Ref(sym)))`, which is
    /// exactly how the loader lowers a value-in-type today (load.rs:5244).
    pub fn make_denoted_occ_ref(
        &self,
        sym: Symbol,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        let value = NodeOccurrence::new_expr(node_occurrence::Expr::Ref(sym), span, owner);
        self.make_denoted_occ(value, span, owner)
    }

    /// `parameterized(base, bindings)` carried as a Type occurrence.
    /// Occurrence peer of [`Self::make_parameterized_type`].
    pub fn make_parameterized_occ(
        &self,
        base: node_occurrence::TypeChild,
        bindings: Vec<(Symbol, node_occurrence::TypeChild)>,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_type(
            node_occurrence::TypeNode::Parameterized { base, bindings },
            span,
            owner,
        )
    }

    /// `named_tuple(fields)` carried as a Type occurrence (WI-342). Occurrence
    /// peer of [`Self::make_named_tuple_type`]; minted when a tuple field's type
    /// is `denoted`-bearing. WI-361: the `(name, type)` children are assembled into
    /// the `Value`-carried `List[NamedTupleElement]` the carrier stores (mirroring the term
    /// form), so the field-type poison rides as `Value::Node` while ground field
    /// types stay `Value::Term`.
    pub fn make_named_tuple_occ(
        &mut self,
        fields: Vec<(Symbol, node_occurrence::TypeChild)>,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        let fields_value = self.build_named_tuple_fields_value(fields);
        NodeOccurrence::new_type(
            node_occurrence::TypeNode::NamedTuple { fields: fields_value },
            span,
            owner,
        )
    }

    /// WI-361: assemble a `named_tuple`'s `(name, type)` children into the
    /// `Value`-carried `List[NamedTupleElement]` the [`node_occurrence::TypeNode::NamedTuple`]
    /// carrier stores — the same shape [`Self::make_named_tuple_type`] builds as a
    /// hash-consed term, but in the `Value` world so a poisoned (`Value::Node`) field
    /// type rides as-is and a ground one stays `Value::Term` (no lift). `cons` cells
    /// and `NamedTupleElement` records are `Value::Entity`s ordered by
    /// [`Self::canonicalize_record_named_args`], matching the term form's discrim/eq key so the
    /// two carriers compare cross-carrier.
    fn build_named_tuple_fields_value(
        &mut self,
        fields: Vec<(Symbol, node_occurrence::TypeChild)>,
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        use node_occurrence::TypeChild;
        let element_sym = self.resolve_symbol("anthill.prelude.NamedTupleElement");
        let name_key = self.intern("name");
        let type_key = self.intern("type");

        let mut elems: Vec<Value> = Vec::with_capacity(fields.len());
        for (field_name, child) in fields {
            let type_value = match child {
                TypeChild::Ground(t) => Value::term(t),
                TypeChild::Node(o) => Value::Node(o),
            };
            let name_ref = Value::term(self.alloc(Term::Ref(field_name)));
            let mut named = vec![(name_key, name_ref), (type_key, type_value)];
            self.canonicalize_record_named_args(element_sym, &mut named);
            elems.push(Value::Entity {
                functor: element_sym,
                pos: Rc::from(Vec::new()),
                named: Rc::from(named),
            });
        }
        // The `cons`/`nil` spine reuses the shared `Value`-list builder (its
        // `[head, tail]` order is canonical, matching `canonicalize_record_named_args`).
        crate::kb::load::build_value_list(self, elems)
    }

    /// `arrow(param, result, effects, arity)` carried as a Type occurrence.
    /// Occurrence peer of [`Self::make_arrow_type`].
    ///
    /// WI-791: `arity` is the parameter-list LENGTH as written — `op.params.len()`
    /// at an eta mint, `params.len()` at a declared signature, the lambda's binder
    /// count at a lambda mint. It is REQUIRED, not derived: deriving it from
    /// `param`'s shape is exactly the ambiguity this ticket closes (a lone
    /// tuple-typed parameter presents the same `named_tuple` an n-parameter list
    /// does). Pass 1 whenever the arrow has a single parameter, INCLUDING when that
    /// parameter's type is itself a tuple.
    pub fn make_arrow_occ(
        &mut self,
        param: node_occurrence::TypeChild,
        result: node_occurrence::TypeChild,
        effects: node_occurrence::TypeChild,
        arity: usize,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        let arity = node_occurrence::TypeChild::Ground(self.make_arity_term(arity));
        self.make_arrow_occ_child(param, result, effects, arity, span, owner)
    }

    /// [`Self::make_arrow_occ`] with the `arity` child already built — for a
    /// REBUILD (projection elimination), which must transplant the arrow's own
    /// arity rather than re-derive a count it no longer has the source for.
    pub(crate) fn make_arrow_occ_child(
        &self,
        param: node_occurrence::TypeChild,
        result: node_occurrence::TypeChild,
        effects: node_occurrence::TypeChild,
        arity: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_type(
            node_occurrence::TypeNode::Arrow { param, result, effects, arity },
            span,
            owner,
        )
    }

    /// WI-791: the arrow `arity` child — a ground `Const(Int)`. Interned like any
    /// other literal, so the occurrence carrier and its hash-consed term twin
    /// carry the SAME child and compare structurally equal.
    ///
    /// `pub` because a test that hand-builds an arrow term (to control its
    /// `effects` child directly, bypassing `make_arrow_type`'s canonicalization)
    /// must still give it an arity — an arrow without one is refused by
    /// `agreed_arrow_arity` before any other child is looked at, which silently
    /// empties such a test of the coverage it was written for.
    pub fn make_arity_term(&mut self, arity: usize) -> TermId {
        self.alloc(Term::Const(crate::kb::term::Literal::Int(arity as i64)))
    }

    /// `effects_rows(effects_expr: EffectExpression)` carried as a Type
    /// occurrence. Occurrence peer of [`Self::make_effects_rows_type`].
    pub fn make_effects_rows_occ(
        &self,
        effects_expr: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_type(
            node_occurrence::TypeNode::EffectsRows { effects_expr },
            span,
            owner,
        )
    }

    /// EffectExpression `present(label)` carried as an occurrence.
    pub fn make_present_occ(
        &self,
        label: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(
            node_occurrence::EffectExprNode::Present { label },
            span,
            owner,
        )
    }

    /// EffectExpression `guarded(label, guard)` carried as an occurrence — minted
    /// when the guarded effect's `label` is `denoted`-bearing (a `Value::Node`).
    /// `guard` is the `Value`-carried `List[reflect.Term]` the
    /// [`node_occurrence::EffectExprNode::Guarded`] carrier stores (build it with
    /// [`crate::kb::load::build_value_list`] over the goal `Value`s — a ground goal
    /// rides as `Value::Term`, a poisoned one as `Value::Node`).
    pub fn make_guarded_occ(
        &self,
        label: node_occurrence::TypeChild,
        guard: crate::eval::value::Value,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(
            node_occurrence::EffectExprNode::Guarded { label, guard },
            span,
            owner,
        )
    }

    /// EffectExpression `absent(label)` carried as an occurrence.
    pub fn make_absent_occ(
        &self,
        label: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(
            node_occurrence::EffectExprNode::Absent { label },
            span,
            owner,
        )
    }

    /// EffectExpression `merge(left, right)` carried as an occurrence.
    pub fn make_merge_occ(
        &self,
        left: node_occurrence::TypeChild,
        right: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(
            node_occurrence::EffectExprNode::Merge { left, right },
            span,
            owner,
        )
    }

    /// EffectExpression `open(tail)` carried as an occurrence.
    pub fn make_open_occ(
        &self,
        tail: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(
            node_occurrence::EffectExprNode::Open { tail },
            span,
            owner,
        )
    }

    /// EffectExpression `empty_row` carried as an occurrence.
    pub fn make_empty_row_occ(
        &self,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(node_occurrence::EffectExprNode::EmptyRow, span, owner)
    }

    /// Convenience: sort_ref from a name string (resolves or interns the name).
    pub fn make_sort_ref_by_name(&mut self, name: &str) -> TermId {
        let sym = if let Some(s) = self.try_resolve_symbol(name) { s } else { self.intern(name) };
        self.make_sort_ref(sym)
    }

    /// `parameterized(base: <type>, bindings: List[TypeBinding])`.
    pub fn make_parameterized_type(&mut self, base: TermId, bindings: &[(Symbol, TermId)]) -> TermId {
        // WI-361 producer flip: term-backed — the base sort IS the functor and the
        // bindings ARE the named args (`List[T = Int]` = `Fn{List, named:[(T, …)]}`),
        // with no `parameterized(base, bindings: List[TypeBinding])` wrapper. The base
        // sort is the discriminating functor (native `rules_by_functor`/discrim
        // selectivity, produced directly). `base` is a sort reference `Ref(S)` (post
        // make_sort_ref flip), read via the reader.
        let base_sym = crate::kb::typing::extract_sort_ref_sym(self, &crate::kb::term_view::TermIdView(base))
            .expect("make_parameterized_type: base must be a sort reference");
        if bindings.is_empty() {
            // A parameterized type with no bindings IS the bare sort (`List[]` ≡
            // `List`) — emit `Ref(S)`, never a degenerate no-arg `Fn{S}` (which
            // `type_head` classifies as `Error`, losing the base sort). Mirrors the
            // inference's own empty-bindings guard; also covers an over-applied
            // non-parametric sort whose stray bindings were dropped at load.
            return self.alloc(Term::Ref(base_sym));
        }
        let named_args: SmallVec<[(Symbol, TermId); 2]> = bindings.iter().copied().collect();
        self.make_entity_term(base_sym, SmallVec::new(), named_args)
    }

    /// `arrow(param: <type>, result: <type>, effects: <effects_rows Type>)`.
    ///
    /// WI-307 v1a row-substrate: `effects` is the singular
    /// `effects_rows(EffectExpression)` Type — not `List[Type]`. The caller
    /// still passes a flat `&[TermId]` of effect labels for ergonomics; we
    /// canonicalize internally (sort by `type_display_name`, dedup, fold into
    /// a right-associated `merge`-chain ending in `empty_row` for closed
    /// rows or `open(tail)` when a `Var::Global` is present). Mixing concrete
    /// labels and a row-tail `Var::Global` in one list is the documented row
    /// shape: `effects { Modify[c], E }` lowers to
    /// `[Modify[c]-term, Var(E)-term]`
    /// → `merge(present(Modify[c]), open(?E))`.
    ///
    /// At most one `Var::Global` is expected (the row tail). Additional
    /// Var::Global past the first are folded as if they were extra labels —
    /// the canonical form still parses, but row unification will treat them
    /// as duplicate tails (semantically nonsensical, but representable).
    /// Var::DeBruijn and Var::Rigid fall through to the labels arm (per
    /// code-review #6) — their unification semantics aren't row-tail.
    ///
    /// **Bootstrap dependency** (code-review #13) — beyond the
    /// `anthill.prelude.TypeExtractor.Arrow` symbol made_arrow_type
    /// needs, this function now also requires
    /// `anthill.prelude.TypeExtractor.EffectsRows` and the five
    /// `anthill.prelude.EffectExpression.{empty_row, present, absent, open,
    /// merge}` entity symbols. All six are pre-registered by
    /// `kb::load::register_stdlib_scopes` (the same path that registers
    /// `TypeExtractor.Arrow`); a KB constructed without `register_prelude` panics
    /// at the first builder call with a clear `resolve_symbol` message
    /// rather than silently producing malformed terms.
    /// WI-791: `arity` is the parameter-list LENGTH as written — see
    /// [`Self::make_arrow_occ`] for why it is a required argument rather than
    /// something read back off `param`.
    pub fn make_arrow_type(
        &mut self,
        param: TermId,
        result: TermId,
        effects: &[TermId],
        arity: usize,
    ) -> TermId {
        let effects_rows_term = self.build_canonical_effects_rows(effects);
        self.make_arrow_from_effects_rows(param, result, effects_rows_term, arity)
    }

    /// Build `arrow(param, result, effects, arity)` from an ALREADY-canonical
    /// `effects_rows(EffectExpression)` Type — the `effects` child is a row, not a
    /// raw label list, so it must NOT be re-canonicalized.
    /// [`Self::make_arrow_type`] canonicalizes a raw label list, then calls this.
    pub(crate) fn make_arrow_from_effects_rows(
        &mut self,
        param: TermId,
        result: TermId,
        effects_rows: TermId,
        arity: usize,
    ) -> TermId {
        let arity_term = self.make_arity_term(arity);
        self.make_arrow_from_effects_rows_arity_term(param, result, effects_rows, arity_term)
    }

    /// [`Self::make_arrow_from_effects_rows`] with the `arity` child already built
    /// — the occurrence→term lowering (`type_node_to_term`) has the exact child the
    /// occurrence carried and must transplant it rather than re-derive a number.
    pub(crate) fn make_arrow_from_effects_rows_arity_term(
        &mut self,
        param: TermId,
        result: TermId,
        effects_rows: TermId,
        arity: TermId,
    ) -> TermId {
        let arrow_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.Arrow");
        let param_key = self.intern("param");
        let result_key = self.intern("result");
        let effects_key = self.intern("effects");
        let arity_key = self.intern("arity");

        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((effects_key, effects_rows));
        named_args.push((param_key, param));
        named_args.push((result_key, result));
        named_args.push((arity_key, arity));
        self.make_entity_term(arrow_sym, SmallVec::new(), named_args)
    }

    // ── EffectExpression builders (WI-307 v1a) ──────────────────────────

    /// EffectExpression `empty_row` — the closed empty row `{}` (pure).
    pub fn make_effect_expression_empty_row(&mut self) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.empty_row");
        self.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// WI-337: bootstrap-safe variant of the
    /// `make_effects_rows_type(make_effect_expression_empty_row())` pair.
    /// Returns `None` when the EffectExpression / `effects_rows` symbols
    /// are not yet registered (i.e. before [`load::register_prelude`] has
    /// run). The panicking variants are convenient for the typer hot
    /// path — `make_arrow_type` and friends require the symbols already
    /// — but `arrow_compatible` / `unify_arrow` can be reached at
    /// bootstrap time on a malformed legacy arrow term that has only one
    /// of `param`/`result`/`effects` populated, in which case the typer
    /// should degrade gracefully rather than crash. The caller decides
    /// the soundness-preserving fallback (typically "reject the missing
    /// side" so the check returns false without claiming compatibility).
    pub fn try_make_empty_effects_rows(&mut self) -> Option<TermId> {
        let empty_sym = self.try_resolve_symbol(
            "anthill.prelude.EffectExpression.empty_row",
        )?;
        let rows_sym = self.try_resolve_symbol(
            "anthill.prelude.TypeExtractor.EffectsRows",
        )?;
        let empty = self.alloc(Term::Fn {
            functor: empty_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let expr_key = self.intern("effects_expr");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((expr_key, empty));
        Some(self.make_entity_term(rows_sym, SmallVec::new(), named_args))
    }

    /// EffectExpression `present(label: Type)` — a single present effect.
    pub fn make_effect_expression_present(&mut self, label: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.present");
        let label_key = self.intern("label");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((label_key, label));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// EffectExpression `guarded(label: Type, guard: List[reflect.Term])` — a
    /// CONDITIONAL present effect (proposal 048 / WI-478). `guard` is an
    /// already-assembled `List[reflect.Term]` term (build it with [`Self::build_list`]
    /// over the guard's goal terms); the degenerate empty guard is the bare
    /// `present(label)` (not produced here). Conservatively present until discharge
    /// (WI-067).
    pub fn make_effect_expression_guarded(&mut self, label: TermId, guard: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.guarded");
        let label_key = self.intern("label");
        let guard_key = self.intern("guard");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((label_key, label));
        named_args.push((guard_key, guard));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// EffectExpression `absent(label: Type)` — `-e` absence guarantee.
    /// Unused in v1a (presence-only); reserved for v1b's `lacks` constraints.
    pub fn make_effect_expression_absent(&mut self, label: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.absent");
        let label_key = self.intern("label");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((label_key, label));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// EffectExpression `open(tail: Type)` — a row variable tail, carrying
    /// the tail `Type` (a `Term::Var` for an unbound row, or a resolved row
    /// type after substitution).
    pub fn make_effect_expression_open(&mut self, tail: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.open");
        let tail_key = self.intern("tail");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((tail_key, tail));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// EffectExpression `merge(left, right)` — union of two expressions.
    /// The canonical row form right-folds present labels into this:
    /// `merge(present(l₁), merge(present(l₂), …, tail))`.
    pub fn make_effect_expression_merge(&mut self, left: TermId, right: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.merge");
        let left_key = self.intern("left");
        let right_key = self.intern("right");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((left_key, left));
        named_args.push((right_key, right));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// Wrap an EffectExpression in the `effects_rows(effects_expr: …)` Type
    /// entity — the bridge from EffectExpression to Type position
    /// (WI-320 substrate). Use this when storing a row in any Type-typed
    /// slot (e.g. `arrow.effects`, `EffectsRuntime[Effects = …]`).
    pub fn make_effects_rows_type(&mut self, expr: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows");
        let expr_key = self.intern("effects_expr");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((expr_key, expr));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// Build a canonical `effects_rows(EffectExpression)` Type from a flat
    /// `&[TermId]` of effect-list elements — the surface representation the
    /// loader and the typer already produce (mixed `Term::Fn` concrete labels
    /// and at most one `Term::Var` row-tail).
    ///
    /// **Canonical form** (so two arrow types with the same effects in
    /// different source order hash-cons to the same TermId):
    ///   - sort labels by `type_display_name` (stable across runs);
    ///   - dedup adjacent identical labels (rows are sets, idempotent);
    ///   - right-fold into `merge(present(l₁), merge(present(l₂), …, tail))`
    ///     where `tail` is `open(?ρ)` if a Var was present, else `empty_row`.
    ///
    /// An empty input list with no tail yields `effects_rows(empty_row)` — the
    /// closed pure row.
    /// WI-441: the row-tail Var a term denotes — the term itself for a bare
    /// `Var::Global` / `Var::Rigid`, the `SortAlias` target Var for a `Ref(S.E)`
    /// (a sort-level row param referenced from an op signature, which lowers as a
    /// Ref). `None` for anything else (a label, a ground type, a `DeBruijn`).
    ///
    /// WI-516: `Var::Rigid` counts as a row tail. An effect-set-valued type param
    /// is rigidified (Skolemized) while an operation body is checked, so a forced/
    /// performed captured effect — a `@ Eff` row whose tail is the op's `Eff`
    /// param — surfaces in the body's inferred effect list as a bare `Var::Rigid`.
    /// Re-canonicalizing that list (here, and at the arrow-occ build site
    /// typing.rs `make_*_occ`) MUST fold it as `open(tail)`, NOT `present(label)`:
    /// a rigid set-valued var is a row VARIABLE, not a single concrete label.
    /// This matches the decompose side (`row_tail_termid` / `effects_rows_to_flat_list`),
    /// which already treat any/bare `Var` as a tail. `Var::DeBruijn` (rule-side,
    /// pre-binder-open; proposal 025 Skolems are minted as Rigid, not DeBruijn)
    /// stays excluded — it never reaches a typed op-signature effect row.
    pub(crate) fn row_tail_var_of(&self, t: TermId) -> Option<TermId> {
        use crate::kb::term::{Term as T, Var as V};
        let is_tail_var = |v: &V| matches!(v, V::Global(_) | V::Rigid(_));
        match self.get_term(t) {
            T::Var(v) if is_tail_var(v) => Some(t),
            T::Ref(sym) => {
                let target = crate::kb::typing::resolve_sort_alias(self, *sym)?;
                match self.get_term(target) {
                    T::Var(v) if is_tail_var(v) => Some(target),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub fn build_canonical_effects_rows(&mut self, effects: &[TermId]) -> TermId {
        // Partition into atoms (`present(label)` / `absent(label)`) and
        // row-tail Var::Global. At most one tail var is expected; if
        // multiple Global vars appear, all-but-the-first are stuffed
        // into the atoms list (canonical form still parses; row
        // unification surfaces the malformed shape).
        //
        // WI-307 code-review #6 / WI-516: `Var::Global` and `Var::Rigid`
        // qualify as row tails (see `row_tail_var_of`). A rigid arises when an
        // effect-set type param is Skolemized during op-body checking; it is a
        // row VARIABLE and folds as `open(tail)`. `Var::DeBruijn` (rule-side,
        // pre-binder-open) stays excluded — it has different unification
        // semantics and never reaches a typed op-signature effect row; it falls
        // through to the atoms arm, where row unification surfaces it as a
        // schema-shape failure rather than a silent mis-classification.
        //
        // WI-327: pre-built `present` / `absent` atoms (e.g. `-E` from
        // surface grammar lowered via `make_effect_expression_absent`)
        // are recognized by their functor symbols and kept as-is. Bare
        // labels are still wrapped in `present(label)`. Mixed input is
        // sorted by display name with the wrapper applied so canonical
        // form is stable regardless of how each atom arrived.
        use crate::kb::term::Term;
        let absent_sym = self.try_resolve_symbol(
            "anthill.prelude.EffectExpression.absent",
        );
        let present_sym = self.try_resolve_symbol(
            "anthill.prelude.EffectExpression.present",
        );
        // WI-478: a `guarded(label, guard)` atom (a ground guarded effect) is, like
        // `present`/`absent`, already a complete EffectExpression atom — keep it
        // as-is rather than wrapping the whole `guarded(…)` Fn in `present(…)`.
        let guarded_sym = self.try_resolve_symbol(
            "anthill.prelude.EffectExpression.guarded",
        );
        let mut atoms: Vec<TermId> = Vec::new();
        // WI-441: ALL row-tail Vars are collected — a row UNION (`{ES, EF}`,
        // the lazy combinators' merge row) folds each as its own `open(…)`.
        // (Pre-WI-441 only the first Var became the tail; the rest were
        // stuffed into the atoms list and wrapped `present(var)` — a
        // malformed shape decompose read as a present LABEL.)
        let mut tail_vars: Vec<TermId> = Vec::new();
        for &e in effects {
            // WI-441: a SORT-level row param referenced in a written row lowers
            // as `Ref(S.E)` (it is not a type param of the CURRENT scope) — its
            // `SortAlias` target Var is the row tail every other reader binds.
            let row_var = self.row_tail_var_of(e);
            match self.get_term(e) {
                _ if row_var.is_some() => {
                    let v = row_var.expect("checked is_some");
                    if !tail_vars.contains(&v) {
                        tail_vars.push(v);
                    }
                }
                Term::Fn { functor, .. }
                    if Some(*functor) == absent_sym
                        || Some(*functor) == present_sym
                        || Some(*functor) == guarded_sym =>
                {
                    // Pre-built EffectExpression atom (WI-327 `-E` →
                    // `absent(E)`, any prior `present(E)` wrapper, or a WI-478
                    // `guarded(label, guard)`). Keep as-is.
                    atoms.push(e);
                }
                _ => {
                    // Bare label — wrap in present().
                    let wrapped = self.make_effect_expression_present(e);
                    atoms.push(wrapped);
                }
            }
        }
        // Canonical ordering: sort by type_display_name, then dedup.
        atoms.sort_by_cached_key(|&t| crate::kb::typing::type_display_name(self, t));
        atoms.dedup();

        // Right-fold: innermost tail first (additional tails as open(…)
        // merges), then merge() walking back through the sorted atom list.
        let mut acc = match tail_vars.first() {
            Some(&tail) => self.make_effect_expression_open(tail),
            None => self.make_effect_expression_empty_row(),
        };
        for &extra_tail in tail_vars.iter().skip(1) {
            let o = self.make_effect_expression_open(extra_tail);
            acc = self.make_effect_expression_merge(o, acc);
        }
        for &atom in atoms.iter().rev() {
            acc = self.make_effect_expression_merge(atom, acc);
        }
        self.make_effects_rows_type(acc)
    }

    /// `type_var(name: <sym>)` — a type variable for inference.
    ///
    /// WI-963 — why a TERM, and why a bare `Var` is not enough. Asked twice; the answer
    /// is checkable, so it lives here and is DRIVEN by
    /// `typing::wi963_type_var_representation_tests` — read those before deleting any
    /// of this as speculation. The whole-system control is recorded there too: making
    /// this function return a bare `Var::Global` stops the stdlib from loading.
    ///
    /// A type is a term in the DECLARED reflect vocabulary — `entity TypeVar(name:
    /// Symbol)` beside `SortRef` / `Parameterized` / the arrow, in
    /// `stdlib/anthill/prelude/sort.anthill` — and `typing::type_head` dispatches on
    /// the functor's qualified name. `Var` is not in that vocabulary: `type_head` reads
    /// `ViewHead::functor_sym()`, which is `None` for a `Var`, so a bare logic var in
    /// type position classifies as `TypeHead::Error`. It would not be an UNKNOWN type,
    /// it would be a MALFORMED one.
    ///
    /// The semantics differ where it matters. A `Var::Global` is a LOGIC variable:
    /// unification BINDS it, and the discrimination tree reads a flex `Global` as a
    /// wildcard edge matching any subterm. A `type_var` is INERT — compatible-with-
    /// anything in the unify/subtype dispatch WITHOUT committing (the M6 flounder
    /// posture on `typing::fresh_type_var`). With a logic var the first unification
    /// turns "this type is undetermined" into "it is now `Int64`" and propagates that
    /// to every occurrence of the same `VarId`; WI-384 states the same at its site
    /// ("a `type_var` WILDCARD (not a bare logic `Var`)").
    ///
    /// Hash-consing it is right, not incidental: the result is keyed by NAME, and every
    /// caller passes one of ~7 literals (`?_`, `?T`, `?param`, …), so the store holds
    /// about seven of these in total — nominal identity, which is what the CLAUDE.md
    /// representation note reserves interning FOR. A `Var::Global` would instead carry a
    /// distinct `VarId` per site, so two undetermined types would not be structurally
    /// equal and each site would have to allocate a fresh var.
    ///
    /// Not a hot path, so do not "optimize" the `resolve_symbol` here: measured at 6
    /// calls for a full stdlib + host-bindings load and type-check, unchanged by a 200×
    /// driver on the unbound-param path (WI-960, rejected on that measurement).
    pub fn make_type_var(&mut self, name: Symbol) -> TermId {
        let type_var_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.TypeVar");
        let name_key = self.intern("name");
        let name_val = self.alloc(Term::Ref(name));
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((name_key, name_val));
        self.make_entity_term(type_var_sym, SmallVec::new(), named_args)
    }

    /// `denoted(value: <term>)` — a value-in-type carried faithfully as a hash-consed
    /// term. The term twin of `TypeNode::Denoted` (WI-390 re-introduced this after
    /// WI-366 retired the ground builder), so a `denoted` round-trips through the
    /// term store. `value` is the ground/qualified reference structure; a local-binder
    /// value rides a `Positioned` internal (see [`Self::make_positioned`]).
    pub fn make_denoted(&mut self, value: TermId) -> TermId {
        let denoted_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.Denoted");
        let value_key = self.intern("value");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((value_key, value));
        self.make_entity_term(denoted_sym, SmallVec::new(), named_args)
    }

    /// `expr_carried(value: <term>, member: Ref(<sym>))` — the term twin of an
    /// expression-carried type projection `s.T` / `s.Sort` (WI-376). `value` is the
    /// receiver occurrence's term (a ground `Ref(s)` for a param/local receiver);
    /// `member` is the projected type-member name, carried as `Ref(sym)` exactly as
    /// [`Self::make_type_var`] carries its `name`. The type-member sibling of
    /// [`Self::make_denoted`]. (A *compound* receiver — `(expr).T` — would instead
    /// ride a `TypeNode::ExprCarried` Node carrier; that surface does not parse yet.)
    pub fn make_expr_carried(&mut self, value: TermId, member: Symbol) -> TermId {
        let expr_carried_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.ExprCarried");
        let value_key = self.intern("value");
        let member_key = self.intern("member");
        let member_val = self.alloc(Term::Ref(member));
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((value_key, value));
        named_args.push((member_key, member_val));
        self.make_entity_term(expr_carried_sym, SmallVec::new(), named_args)
    }

    /// `rigid_type_projection(sort: Ref(<decl>), var: <subject>, member: Ref(<sym>))` —
    /// the TYPE-receiver projection `P.Key` / `MemStore.Key` (WI-428, design §5.3): the
    /// type-keyed sibling of [`Self::make_expr_carried`]. `subject` is the projection's
    /// receiver TERM — `Ref(P)` for a rigid type-parameter, `Ref(S)` for a concrete
    /// sort; `decl_sort` is the sort whose `requires` chain lends the subject its
    /// members (= the subject itself for a concrete-sort subject — the discriminator
    /// the eliminator uses). All three slots are ground, so the projection always
    /// hash-conses (no Node carrier).
    pub fn make_rigid_projection(
        &mut self,
        decl_sort: Symbol,
        subject: TermId,
        member: Symbol,
    ) -> TermId {
        let functor = self.resolve_symbol("anthill.prelude.TypeExtractor.RigidTypeProjection");
        let sort_key = self.intern("sort");
        let var_key = self.intern("var");
        let member_key = self.intern("member");
        let sort_val = self.alloc(Term::Ref(decl_sort));
        let member_val = self.alloc(Term::Ref(member));
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((sort_key, sort_val));
        named_args.push((var_key, subject));
        named_args.push((member_key, member_val));
        self.make_entity_term(functor, SmallVec::new(), named_args)
    }

    /// Occurrence twin of [`Self::make_expr_carried`] for a COMPOUND receiver
    /// (`a.b.T`): the receiver is a field-access `Expr` occurrence (a `DotApply`
    /// chain over the value path) that cannot hash-cons, so the whole projection
    /// rides a [`node_occurrence::TypeNode::ExprCarried`] Node carrier rather than a
    /// ground term. `receiver` is that field-path occurrence; `member` the projected
    /// type-member name, carried as a ground `Ref` child exactly as the term form
    /// does — so `TermView` reads `value` / `member` identically across carriers, and
    /// `extract_type` yields the same `TypeExtractor::ExprCarried`. WI-397.
    pub fn make_expr_carried_occ(
        &mut self,
        receiver: std::rc::Rc<node_occurrence::NodeOccurrence>,
        member: Symbol,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> std::rc::Rc<node_occurrence::NodeOccurrence> {
        let member_ref = self.alloc(Term::Ref(member));
        node_occurrence::NodeOccurrence::new_type(
            node_occurrence::TypeNode::ExprCarried {
                value: node_occurrence::TypeChild::Node(receiver),
                member: node_occurrence::TypeChild::Ground(member_ref),
            },
            span,
            owner,
        )
    }

    /// Positioned(pos, internal) — a local-binder reference (a lambda parameter /
    /// `let`-local, scope-local and not globally unique) carried with its absolute
    /// binding-site identity `pos`, so two distinct locals with the same surface name
    /// don't collide as one hash-consed term. WI-390: `Positioned` is leaf-only (it
    /// wraps a binder leaf, never a compound) and unifies structurally as an ordinary
    /// `Term::Fn`; the type-level alpha-equivalence reading is deferred.
    pub fn make_positioned(&mut self, pos: TermId, internal: TermId) -> TermId {
        let positioned_sym = self.resolve_symbol("anthill.reflect.Positioned");
        let pos_key = self.intern("pos");
        let internal_key = self.intern("internal");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((pos_key, pos));
        named_args.push((internal_key, internal));
        self.make_entity_term(positioned_sym, SmallVec::new(), named_args)
    }

    /// `named_tuple(fields: List[NamedTupleElement])`.
    pub fn make_named_tuple_type(&mut self, fields: &[(Symbol, TermId)]) -> TermId {
        let named_tuple_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.NamedTuple");
        let element_sym = self.resolve_symbol("anthill.prelude.NamedTupleElement");
        let fields_key = self.intern("fields");
        let name_key = self.intern("name");
        let type_key = self.intern("type");

        let field_terms: Vec<TermId> = fields.iter().map(|(field_name, field_type)| {
            let name_ref = self.alloc(Term::Ref(*field_name));
            let mut args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            args.push((name_key, name_ref));
            args.push((type_key, *field_type));
            self.make_entity_term(element_sym, SmallVec::new(), args)
        }).collect();

        let fields_list = self.build_list(&field_terms);

        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((fields_key, fields_list));
        self.make_entity_term(named_tuple_sym, SmallVec::new(), named_args)
    }

    /// nothing — bottom type.
    pub fn make_nothing_type(&mut self) -> TermId {
        let nothing_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.Nothing");
        self.alloc(Term::Fn {
            functor: nothing_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    // ── Name-level substitution ──────────────────────────────────

    /// Replace all occurrences of `from` with `to` throughout a term's structure.
    /// Returns a new hash-consed TermId (may be the same if no replacement occurred).
    pub fn subst_term(&mut self, term: TermId, from: TermId, to: TermId) -> TermId {
        if term == from {
            return to;
        }
        self.map_fn_children(term, |kb, id| kb.subst_term(id, from, to))
    }

    /// Apply multiple substitutions (from → to) to a term.
    pub fn subst_term_multi(&mut self, mut term: TermId, bindings: &[(TermId, TermId)]) -> TermId {
        for &(from, to) in bindings {
            term = self.subst_term(term, from, to);
        }
        term
    }

    // ── Entity field registry ──────────────────────────────────

    /// Register the ordered field names for an entity functor.
    ///
    /// FIELD NAMES ARE EXPECTED DISTINCT (WI-808) and this does NOT check it — the rule
    /// is enforced at the syntax layer, in `convert_entity`, which is the only place a
    /// user-written entity comes from (`register_entity_field_names_scan` maps that
    /// `Entity`'s own fields). It is stated here because the other callers are SYNTHETIC
    /// kernel entities built in Rust with hardcoded field vectors, which the parse guard
    /// cannot see: they are distinct today, and a future one that is not would reintroduce
    /// the defect silently — `x.f`, a named argument, and a rule pattern all resolve a
    /// field name to its FIRST match, so the later field becomes unaddressable by name.
    /// No check here because there is no span or error channel at this layer to report
    /// against; the constraint belongs to whoever writes the vector.
    pub fn register_entity_fields(&mut self, functor: Symbol, fields: Vec<Symbol>) {
        self.entity_fields.insert(functor, fields);
    }

    /// Look up the ordered field names for an entity functor.
    pub fn entity_field_names(&self, functor: Symbol) -> Option<&[Symbol]> {
        self.entity_fields.get(&functor).map(|v| v.as_slice())
    }

    /// Register entity field types: functor → [(field_name, type)]. WI-342: the
    /// field type is carrier-agnostic — a `denoted`-bearing field type (a
    /// value-in-type / dependent field) rides as `Value::Node`, a ground field
    /// type as `Value::Term`.
    pub fn register_entity_field_types(&mut self, functor: Symbol, fields: Vec<(Symbol, crate::eval::value::Value)>) {
        self.entity_field_types.insert(functor, fields);
    }

    /// Look up the field types for an entity functor (carrier-agnostic `Value`).
    pub fn entity_field_types(&self, functor: Symbol) -> Option<&[(Symbol, crate::eval::value::Value)]> {
        self.entity_field_types.get(&functor).map(|v| v.as_slice())
    }

    /// Iterate all functor symbols that have registered field types.
    pub fn entity_field_type_functors(&self) -> impl Iterator<Item = &Symbol> {
        self.entity_field_types.keys()
    }

    /// WI-835 — record one written parameterized type instantiation, for the
    /// post-load use-site checks. Called from the type lowerings; see
    /// [`ParameterizedSite`] and the `parameterized_type_sites` field comment.
    /// A site with no ground bindings is not recorded — there is nothing to
    /// check, and `make_parameterized_type` collapses an empty binding list to a
    /// bare `Ref(base)` anyway (`List[]` ≡ `List`, and the over-applied
    /// non-parametric case), so recording one would bank an entry every reader
    /// must then discard.
    pub(crate) fn record_parameterized_type_site(&mut self, site: ParameterizedSite) {
        if site.bindings.is_empty() {
            return;
        }
        self.parameterized_type_sites.push(site);
    }

    /// WI-835 — take the recorded sites, leaving the registry empty. DRAINING, so
    /// a later `load_incremental` into this KB checks only its own sites instead
    /// of re-walking (and re-reporting) every batch loaded before it.
    pub(crate) fn take_parameterized_type_sites(&mut self) -> Vec<ParameterizedSite> {
        std::mem::take(&mut self.parameterized_type_sites)
    }

    /// Check if a functor symbol is a constructor (entity with a parent sort).
    /// O(1) lookup via pre-built index populated by register_entity_of.
    pub fn is_constructor_symbol(&self, functor: Symbol) -> bool {
        self.constructor_symbols.contains(&functor)
    }

    /// WI-720: mark a functor SYMBOL as a constructor, WITHOUT the parent-sort /
    /// field registration [`Self::register_entity_of`] additionally performs.
    /// `scan_definitions` pass 1 calls this for every sort-nested `entity`, so
    /// `is_constructor_symbol` — and with it the order-dependent alloc/discrim
    /// `Fn{c,[],[]}`→`Ref(c)` canon ([`Self::alloc`]) — is settled before ANY
    /// fact/rule body converts. Because pass 1 defines every name across every
    /// file before any body loads, this makes the canon load-order-independent
    /// for EVERY constructor (WI-719 pre-registered only the four prelude ones).
    /// The parent/field indexes (`entity_parent`, `sort_entities`) are still
    /// populated later by `register_entity_of` when the sort body loads.
    pub fn mark_constructor_symbol(&mut self, functor: Symbol) {
        self.constructor_symbols.insert(functor);
    }

    /// WI-352 — whether `sym` is an operation's reserved `result` binder
    /// (`<op>.result`, proposal 041), by its **symbol kind**. WI-341 first
    /// moved this off a spelling match (`rsplit('.') == "result"`) onto symbol
    /// identity; WI-351 used a `PlaceRole` side-table; WI-352 makes the kind
    /// itself carry the truth, so this is exactly `kind == OpResult`. Keeps
    /// `Cell.new.result` masking (WI-314) unchanged.
    pub(crate) fn is_result_binder(&self, sym: Symbol) -> bool {
        self.kind_of(sym) == Some(crate::intern::SymbolKind::OpResult)
    }

    /// A free-standing entity: declared at namespace level (registered fields)
    /// with no parent sort, so it is not a constructor. A bare reference to one
    /// denotes the entity as a type rather than a construction.
    pub fn is_free_standing_entity(&self, functor: Symbol) -> bool {
        self.entity_field_types(functor).is_some() && !self.is_constructor_symbol(functor)
    }

    /// Does an APPLICATION of `functor` construct an entity value? True for a
    /// sort-nested constructor ([`Self::is_constructor_symbol`]) and for an
    /// entity that is its own type — a free-standing `entity E(…)` and, since
    /// WI-926 (§6.3), an eponymous `sort E { entity E(…) }`, which is the same
    /// declaration written the long way. The shared answer is the declared FIELD
    /// SCHEMA: a symbol that has one is constructible, whatever route declared it.
    ///
    /// Read the schema by NAMES, not types: names are registered in
    /// `scan_definitions` pass 1 and types during the load, so this stays
    /// load-order-independent.
    ///
    /// APPLIED position only. A BARE reference does NOT share this reading — a
    /// bare eponymous/free-standing entity name denotes the entity as a *type*
    /// (`check_bare_ref`'s `is_free_standing_entity` arm and its eval twin), which
    /// is why those sites keep the narrower `is_constructor_symbol` test.
    ///
    /// RESOLVED symbols only, and that guard is load-bearing (measured): the field
    /// registry is ALSO keyed under the bare-interned SHORT name — the second key
    /// `register_entity_field_names_scan` writes for sugar-generated facts — so an
    /// UNRESOLVED symbol would answer `true` for any name whose last segment
    /// happens to match some entity's. That is short-name IDENTITY matching, which
    /// WI-672 eliminated. Without the guard, an out-of-scope bare `box(value: 1)`
    /// (an unresolved name, which must reach the typer's scoping diagnostic)
    /// silently constructed `Box.box` instead.
    pub fn is_entity_constructor(&self, functor: Symbol) -> bool {
        if self.is_constructor_symbol(functor) {
            return true;
        }
        self.kind_of(functor).is_some() && self.entity_field_names(functor).is_some()
    }

    // ── Builtin dispatch ────────────────────────────────────────

    /// Bind one fully-qualified stdlib operation name to its [`BuiltinTag`].
    /// Creates a resolved definition if the name isn't already defined.
    /// Derives the proper scope from the namespace prefix of the qualified name.
    ///
    /// WI-968 — named for the tag, because
    /// [`Interpreter::register_builtin`](crate::eval::Interpreter::register_builtin)
    /// binds a host Rust fn under the bare name. `pub(crate)`: the only caller is
    /// [`Self::register_builtin_tags`], and `BuiltinTag` is a closed enum, so this
    /// is no extension point.
    pub(crate) fn register_builtin_tag(&mut self, qualified_name: &str, tag: BuiltinTag) {
        let sym = if let Some(&resolved) = self.symbols.by_qualified_name.get(qualified_name) {
            resolved
        } else {
            let short = qualified_name.rsplit('.').next().unwrap_or(qualified_name);
            // Find scope from namespace prefix (e.g. "anthill.reflect.typing" for
            // "anthill.reflect.typing.is_entity_of")
            let ns_sym_opt = if let Some(dot_pos) = qualified_name.rfind('.') {
                let ns_prefix = &qualified_name[..dot_pos];
                self.symbols.by_qualified_name.get(ns_prefix).copied()
            } else {
                None
            };
            let scope = if let Some(ns_sym) = ns_sym_opt {
                self.symbols.scope_id(ns_sym)
            } else {
                panic!(
                    "register_builtin_tag: namespace prefix for '{}' not found. \
                     Call register_prelude() first to create the namespace hierarchy.",
                    qualified_name
                )
            };
            self.symbols.define(short, qualified_name, SymbolKind::Operation, scope)
        };
        self.builtins.insert(sym, tag);
    }

    /// Register the builtin TAGS — each entry binds a fully-qualified stdlib
    /// operation name to the [`BuiltinTag`] the resolver dispatches on. No host
    /// code is bound here.
    ///
    /// WI-967 — a STEP OF BOOTSTRAP, not a peer of it.
    /// [`load::register_prelude`] is its ONE
    /// caller and owns the ordering (this needs the namespace hierarchy
    /// `register_stdlib_scopes` creates — [`Self::register_builtin_tag`] panics
    /// without it). A caller-side call is therefore always redundant; 218 were
    /// deleted under WI-967, every one of them sitting beside a `register_prelude`
    /// or a load entry point that had already run it.
    ///
    /// `pub(crate)` SO THEY CANNOT COME BACK. It was `pub`, which is what let the
    /// redundant line spread to 172 files; narrowing it makes the whole class
    /// unrepresentable outside this crate instead of merely documented. If you are
    /// reaching for it, you want `register_prelude`.
    ///
    /// WI-968 — `builtin_tag`, not `builtin`, because
    /// [`crate::eval::builtins::register_standard_builtins`] claims the other half
    /// of that word: a free function binding host fns on an `Interpreter`, re-run
    /// per fresh interpreter. It kept the shared name — it is the one with call
    /// sites throughout the suite while this has exactly one, and being a free
    /// function it is also the only one of the two that can be imported bare and
    /// misread. This side now says which registry it writes.
    pub(crate) fn register_builtin_tags(&mut self) {
        self.register_builtin_tag("anthill.reflect.nonvar", BuiltinTag::NonVar);
        self.register_builtin_tag("anthill.reflect.ground", BuiltinTag::Ground);
        self.register_builtin_tag("anthill.reflect.qualified_name", BuiltinTag::QualifiedName);
        self.register_builtin_tag("anthill.reflect.short_name", BuiltinTag::ShortName);
        self.register_builtin_tag("anthill.reflect.lookup_symbol", BuiltinTag::LookupSymbol);
        self.register_builtin_tag("anthill.reflect.not", BuiltinTag::Not);
        self.register_builtin_tag("anthill.reflect.typing.is_entity_of", BuiltinTag::IsEntityOf);
        self.register_builtin_tag("anthill.reflect.typing.extract_sort_ref", BuiltinTag::ExtractSort);
        // WI-860 (058 §3.6) — the provision classifier behind `self_provides` /
        // `default_provider`.
        self.register_builtin_tag("anthill.reflect.typing.dispatch_carrier", BuiltinTag::DispatchCarrier);
        self.register_builtin_tag("anthill.reflect.resolve_sort_instantiation_param", BuiltinTag::ResolveSortInstParam);
        self.register_builtin_tag("anthill.reflect.scope", BuiltinTag::Scope);
        self.register_builtin_tag("anthill.reflect.kind", BuiltinTag::Kind);
        self.register_builtin_tag("anthill.reflect.feed.provenance", BuiltinTag::Provenance);
        self.register_builtin_tag("anthill.reflect.field_access", BuiltinTag::FieldAccess);
        self.register_builtin_tag("anthill.reflect.Expr.ho_apply", BuiltinTag::HoApply);
        // Resolver primitives (proposal 033 / 033.1 / 049)
        self.register_builtin_tag("anthill.kernel.push_choice", BuiltinTag::PushChoice);
        self.register_builtin_tag("anthill.kernel.cut", BuiltinTag::Cut);
        self.register_builtin_tag("anthill.kernel.unify", BuiltinTag::Unify);
        // WI-300 — rule-body requirement guard. A rule-body `requires(X)` desugars
        // (converter) to `find_dictionary(X)`; the typer sweep rewrites the argument
        // to carry spec X's base symbol plus the rule vars that ground its
        // type-parameters. Guard tier: checks `provides` at the current binding,
        // suspends-as-residual on an under-determined carrier.
        self.register_builtin_tag("anthill.kernel.find_dictionary", BuiltinTag::FindDictionary);
        // Arithmetic and comparison. WI-616 (proposal 051 Phase 2): `=`/`eq`
        // and `neq` are the SEMANTIC `Eq` ops — structural until a carrier
        // declares its own `eq` override (`Set.eq`/`Map.eq`), which then
        // dispatches at SLD. `===` (struct_eq, WI-615) keeps the structural
        // `builtin_eq`: total, carrier-agnostic, never dispatches.
        // WI-644 / proposal 004: eq/neq live on PartialEq, gt/lt/gte/lte on
        // PartialOrd (the partial bases); Eq/Ordered are the lawful/total markers.
        self.register_builtin_tag("anthill.prelude.PartialEq.eq", BuiltinTag::SemEq);
        self.register_builtin_tag("anthill.kernel.struct_eq", BuiltinTag::Eq);
        self.register_builtin_tag("anthill.prelude.PartialEq.neq", BuiltinTag::SemNeq);
        self.register_builtin_tag("anthill.prelude.PartialOrd.gt", BuiltinTag::Gt);
        self.register_builtin_tag("anthill.prelude.PartialOrd.lt", BuiltinTag::Lt);
        self.register_builtin_tag("anthill.prelude.PartialOrd.gte", BuiltinTag::Gte);
        self.register_builtin_tag("anthill.prelude.PartialOrd.lte", BuiltinTag::Lte);
        // WI-876 — the same four, keyed to each SCALAR CARRIER that now declares them
        // as its own operations. A bare `gt(?a, 0)` in a rule inside `sort Int64`
        // resolves to `Int64.gt`, not to the spec op, so without these entries the
        // resolver would lose a comparison it has always had. `builtin_cmp` is the
        // same numeric comparator for all of them.
        //
        // WHAT THIS REGISTRY IS NOT: the evaluator's, which WI-876 made read the
        // `operation_map` facts. Two things stayed here that should not have, and
        // both are WI-879 — stated plainly because a half-migration reads as a
        // finished one:
        //
        //   * THE FOUR SPEC-OP ENTRIES ABOVE ARE STILL LIVE. WI-876 ADDED the carrier
        //     entries beside them; it did not delete them, because a bare `gt(?x, 5)`
        //     in any other namespace still resolves to `PartialOrd.gt`. So at SLD the
        //     ticket's own defect stands: MEASURED, `PartialOrd.gt("b", "a")` as a
        //     rule-body goal yields NO SOLUTIONS — `builtin_cmp` reads NUMERIC
        //     operands only and returns `Failure` on a string pair — while the same
        //     comparison in eval answers `true`. The new `String.gt` entry inherits
        //     that, claiming no more and no less than the spec op did.
        //   * THE LIST IS STILL HARDCODED, and "it runs before `load_all`" is why
        //     THIS function cannot read the facts — not why the list must be written
        //     by hand. `load::build_host_op_mappings` is a post-load pass holding
        //     `&mut KnowledgeBase`, and `register_builtin_tag` is a `&mut self` method,
        //     so the derivation site exists. Until it is taken, this array must be
        //     hand-synced with four `.anthill` files in another crate.
        // Spelled out rather than built with `format!`: this runs once per KB and the
        // suite builds thousands, and a `&'static str` costs nothing.
        for (qn, tag) in [
            ("anthill.prelude.Int64.gt", BuiltinTag::Gt),
            ("anthill.prelude.Int64.lt", BuiltinTag::Lt),
            ("anthill.prelude.Int64.gte", BuiltinTag::Gte),
            ("anthill.prelude.Int64.lte", BuiltinTag::Lte),
            ("anthill.prelude.BigInt.gt", BuiltinTag::Gt),
            ("anthill.prelude.BigInt.lt", BuiltinTag::Lt),
            ("anthill.prelude.BigInt.gte", BuiltinTag::Gte),
            ("anthill.prelude.BigInt.lte", BuiltinTag::Lte),
            ("anthill.prelude.String.gt", BuiltinTag::Gt),
            ("anthill.prelude.String.lt", BuiltinTag::Lt),
            ("anthill.prelude.String.gte", BuiltinTag::Gte),
            ("anthill.prelude.String.lte", BuiltinTag::Lte),
            ("anthill.prelude.Float.gt", BuiltinTag::Gt),
            ("anthill.prelude.Float.lt", BuiltinTag::Lt),
            ("anthill.prelude.Float.gte", BuiltinTag::Gte),
            ("anthill.prelude.Float.lte", BuiltinTag::Lte),
        ] {
            self.register_builtin_tag(qn, tag);
        }
        self.register_builtin_tag("anthill.prelude.Numeric.add", BuiltinTag::Add);
        self.register_builtin_tag("anthill.prelude.Numeric.sub", BuiltinTag::Sub);
        self.register_builtin_tag("anthill.prelude.Numeric.mul", BuiltinTag::Mul);
        // div/mod live on Int64 (division is not total on Numeric); the `/` `div`
        // `%` `mod` operators desugar to the bare names, resolved to these
        // registrations so a query computes them (WI-863). divExact aliases div (a
        // stdlib rule); it is registered for the QUALIFIED form but deliberately
        // kept out of PRELUDE_QUALIFIED — no operator mints a bare `divExact`.
        self.register_builtin_tag("anthill.prelude.Int64.div", BuiltinTag::Div);
        self.register_builtin_tag("anthill.prelude.Int64.divExact", BuiltinTag::Div);
        self.register_builtin_tag("anthill.prelude.Int64.mod", BuiltinTag::Mod);
        // Conversions
        self.register_builtin_tag("anthill.prelude.BigInt.to_bigint", BuiltinTag::ToBigInt);
        self.register_builtin_tag("anthill.prelude.BigInt.to_int", BuiltinTag::ToInt);

        // Occurrence builtins (stubs — full implementations in future phases)
        self.register_builtin_tag("anthill.reflect.occurrence_term", BuiltinTag::OccurrenceTerm);
        self.register_builtin_tag("anthill.reflect.occurrence_span", BuiltinTag::OccurrenceSpan);
        self.register_builtin_tag("anthill.reflect.occurrence_owner", BuiltinTag::OccurrenceOwner);
        self.register_builtin_tag("anthill.reflect.sub_occurrences", BuiltinTag::SubOccurrences);
        self.register_builtin_tag("anthill.reflect.operation_body", BuiltinTag::OperationBody);
        // WI-627: cache the equality-connective symbols now that they're defined.
        self.cache_connective_syms();
    }

    /// Re-resolve builtins after scan_definitions().
    /// If scan_definitions created a new resolved symbol for a builtin's
    /// qualified name (from .anthill source), remap the builtin to use it.
    pub fn resolve_builtins(&mut self) {
        let old: Vec<(Symbol, BuiltinTag)> = self.builtins.drain().collect();
        for (old_sym, tag) in old {
            let qualified = match self.symbols.get(old_sym) {
                SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                SymbolDef::Unresolved { name } => name.clone(),
            };
            let sym = self.symbols.by_qualified_name.get(&qualified)
                .copied().unwrap_or(old_sym);
            self.builtins.insert(sym, tag);
        }
        // WI-627: a builtin's canonical symbol may have been remapped above;
        // re-sync the equality-connective cache to the final symbols.
        self.cache_connective_syms();
    }

    /// True iff `sym` is a registered resolver builtin (`anthill.prelude.PartialEq.eq`,
    /// `Numeric.add`, …). WI-363: a spec op that maps to a builtin is backed by
    /// the host primitive, not an anthill body/rule — so the op-provision check
    /// must treat it as satisfied.
    pub fn is_builtin(&self, sym: Symbol) -> bool {
        self.builtins.contains_key(&sym)
    }

    /// WI-876 — does `sym` name an operation a binding block gave a HOST
    /// implementation (an `operation_map` entry), IN ANY LANGUAGE? Such a member is
    /// deliberately body-LESS in anthill — its body is the host artifact's — so a
    /// reader asking "does an implementation exist?" must count it, or it reads as
    /// unimplemented. Populated by `load::build_host_op_mappings`.
    ///
    /// Language-AGNOSTIC, matching the cache it is built from: the question is about
    /// the PROGRAM, and a cpp-only mapping still means the author supplied an
    /// implementation. The LOAD CHECK (`typing::op_is_executable`) is the reader that
    /// wants this. Eval must not — see [`Self::is_interpreter_mapped_op`].
    ///
    /// Sits on the dispatch path, so the two cheap answers come first: no mappings at
    /// all — every KB that loads no binding block — and then the RAW symbol, which is
    /// the common case because [`Self::set_host_op_mappings`] canonicalizes on insert.
    /// Canonicalizing here hashes the operation's whole qualified name, so it is left
    /// to the miss.
    pub fn is_host_mapped_op(&self, sym: Symbol) -> bool {
        if self.host_mapped_ops.is_empty() {
            return false;
        }
        self.host_mapped_ops.contains(&sym)
    }

    /// WI-886 — [`Self::is_host_mapped_op`] NARROWED TO `lang == "rust"`: does this
    /// process's interpreter have a host implementation registered for `sym`?
    ///
    /// The two questions were one index while every `operation_map` in the tree named
    /// rust functions, and WI-876's own doc on `set_host_op_mappings` states the
    /// invariant the merged index broke as soon as a second language appeared:
    /// "this predicate promises the INTERPRETER has an implementation, and the
    /// interpreter's builtin map is a RAW `Symbol` lookup". `register_operation_mappings`
    /// registers `lang == "rust"` entries and skips the rest, so a cpp-only mapping
    /// made the promise for an operation eval has nothing for — `carrier_override_op`
    /// would select it as a carrier's own implementation and skip the spec default
    /// that would have worked. WI-886 gives cpp-gen real `operation_map` data, which
    /// is what makes that live.
    ///
    /// The language is [`load::INTERPRETER_LANG`], which is also what
    /// `builtins::register_operation_mappings` filters by — one owner, because the two
    /// agreeing IS this predicate's promise.
    pub fn is_interpreter_mapped_op(&self, sym: Symbol) -> bool {
        if self.interpreter_mapped_ops.is_empty() {
            return false;
        }
        self.interpreter_mapped_ops.contains(&sym)
    }

    /// WI-876 — the cached `operation_map` entries, in load order. Read by the host
    /// runtime's builtin registration, which needs the host function name as well
    /// as the operation. See `load::build_host_op_mappings` for why it is cached.
    pub fn host_op_mappings(&self) -> &[load::HostOperationMapping] {
        &self.host_op_mappings
    }

    /// WI-889 — the cached `const_map` entries, in load order. Read by the rust
    /// runtime's `register_const_mappings` (which registers the `lang == "rust"`
    /// value sources) and by cpp-gen's `HostConstTable` (which keeps the `lang ==
    /// "cpp"` expressions). See `load::build_host_const_mappings` for why it is cached.
    pub fn host_const_mappings(&self) -> &[load::HostConstMapping] {
        &self.host_const_mappings
    }

    /// Replace the const-mapping cache. Sole caller: `load::build_host_const_mappings`.
    /// No membership index to rebuild — a const is a `force_const` value source, not a
    /// dispatch target — so this is a plain store, unlike `set_host_op_mappings`.
    pub(crate) fn set_host_const_mappings(&mut self, mappings: Vec<load::HostConstMapping>) {
        self.host_const_mappings = mappings;
    }

    /// Replace the host-mapping cache and the TWO membership indexes derived from it.
    /// Sole caller: `load::build_host_op_mappings`.
    /// BOTH SPELLINGS of each mapped operation are indexed — the symbol
    /// `try_resolve_symbol` returned and its canonical twin — because one qualified
    /// name can be interned under several `Symbol`s, and the reader that consumes this
    /// (`typing::op_is_interpretable`, on the dispatch path) may be handed either. The
    /// eq-dispatch index keys under both spellings for the same reason.
    ///
    /// A LOOKUP-ONLY fallback would be wrong here: the interpreter-side predicate
    /// promises the INTERPRETER has an implementation, and the interpreter's builtin
    /// map is a RAW `Symbol` lookup. Answering `true` for a spelling that map does not
    /// hold would select a carrier override the evaluator then cannot find, skipping a
    /// spec default that would have worked. So the two are populated in step —
    /// `register_operation_mappings` registers under both spellings too.
    ///
    /// WI-886 — and for the same reason the LANGUAGE must split them: the interpreter
    /// registers `lang == "rust"` entries only, so a cpp mapping belongs in the
    /// program-wide index and NOT in the interpreter's.
    pub(crate) fn set_host_op_mappings(&mut self, mappings: Vec<load::HostOperationMapping>) {
        let mut index = std::collections::HashSet::new();
        let mut interp_index = std::collections::HashSet::new();
        for m in &mappings {
            let Some(sym) = m.op else { continue };
            let canon = self.canonical_sym(sym);
            index.insert(sym);
            index.insert(canon);
            if m.lang == load::INTERPRETER_LANG {
                interp_index.insert(sym);
                interp_index.insert(canon);
            }
        }
        self.host_mapped_ops = index;
        self.interpreter_mapped_ops = interp_index;
        self.host_op_mappings = mappings;
    }

    /// Is `s` the prelude `Bool` sort, compared by SHORT name (robust to how
    /// `Bool` is qualified / re-exported)? The single definition of "this sort
    /// is `Bool`" shared by the resolver's goal-routing gate
    /// ([`Self::bare_bodied_bool_relation`]) and the typer's static goal check
    /// (`check_rule_body_goal_ops`), so the two cannot drift on how `Bool` is
    /// recognized. A hypothetical user sort also named `Bool` is treated
    /// identically by both — harmless: it merely lets a bare goal route to
    /// `= true` rather than being flagged, never a wrong answer.
    pub(crate) fn sort_sym_is_bool(&self, s: Symbol) -> bool {
        self.local_name_of(s).rsplit('.').next() == Some("Bool")
    }

    /// Check if a goal term's functor is a registered builtin.
    /// Returns `Some(tag)` if so, `None` otherwise.
    pub fn get_builtin(&self, goal: TermId) -> Option<BuiltinTag> {
        self.get_builtin_view(&term_view::TermIdView(goal))
    }

    /// `get_builtin` generic over the goal representation — classifies a goal
    /// by the builtin table from the functor read through [`term_view::TermView`], so a
    /// `Value::Node` occurrence goal (WI-246) is dispatched without lowering.
    pub fn get_builtin_view<V: term_view::TermView>(&self, goal: &V) -> Option<BuiltinTag> {
        match goal.head(self) {
            term_view::ViewHead::Functor { functor: Some(sym), .. } => self.builtin_of(sym),
            _ => None,
        }
    }

    /// The builtin tag registered for `functor`, read by SYMBOL — the functor-keyed
    /// face of [`Self::get_builtin_view`], for a caller that holds a head symbol and
    /// no goal to view (WI-730's row-lambda compiler classifies a candidate predicate
    /// head before it builds the atom). One table, read in one place.
    pub fn builtin_of(&self, functor: Symbol) -> Option<BuiltinTag> {
        self.builtins.get(&functor).copied()
    }
}

impl Default for KnowledgeBase {
    fn default() -> Self {
        Self::new()
    }
}

impl TermSource for KnowledgeBase {
    fn term(&self, id: TermId) -> &Term {
        self.terms.get(id)
    }
    fn sym_name(&self, sym: Symbol) -> &str {
        self.symbols.local_name(sym)
    }
    fn qualified_name(&self, sym: Symbol) -> &str {
        self.qualified_name_of(sym)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use term::Literal;
    use smallvec::SmallVec;

    // ── WI-969: a KB without the prelude ─────────────────────────
    //
    // A bare `KnowledgeBase::new()` is still constructible and still a defined
    // configuration — these are its smoke tests. What changed in WI-969 is what
    // it does when asked for kernel vocabulary it does not have: `eq_functor` /
    // `unify_functor` used to invent a bare `intern("eq")` / `intern("unify")`,
    // a SECOND spelling of the canonical head that no loaded KB can ever
    // produce. Its failure mode was the worst kind — a `[simp]` rule built on
    // the bare spelling simply never matched, so the rewrite silently did not
    // happen (WI-283). Now the KB says so.
    //
    // CONTROL: `bootstrapped_kb_resolves_the_canonical_equality_head` below is
    // the other half — without it these two would also pass if the accessors
    // panicked unconditionally. Both `#[should_panic]` tests fail (they stop
    // panicking) if the `unwrap_or_else` fallbacks are restored.

    #[test]
    #[should_panic(expected = "never bootstrapped")]
    fn bare_kb_eq_functor_is_loud() {
        let mut kb = KnowledgeBase::new();
        kb.eq_functor();
    }

    #[test]
    #[should_panic(expected = "never bootstrapped")]
    fn bare_kb_unify_functor_is_loud() {
        let mut kb = KnowledgeBase::new();
        kb.unify_functor();
    }

    #[test]
    fn bare_kb_does_not_classify_a_short_named_eq_as_the_connective() {
        // WI-969 — the CONTROL for the removed SHORT-NAME arm, and the only test
        // that fails if it comes back. With no canonical connective cached, an
        // `eq`-NAMED head is not the equality connective; the deleted fallback
        // compared short names and answered `true` here. The same comparison, on a
        // loaded KB whose cache had not been filled, would classify a carrier's own
        // `Map.eq`/`Set.eq` as an equational law — unindexing it (WI-139) and
        // dropping it from SLD candidates. That is the WI-627 bug.
        let mut kb = KnowledgeBase::new();
        let domain = kb.intern("test");
        let eq_named = kb.intern("eq");
        let one = kb.alloc(Term::Const(Literal::Int(1)));
        let head = kb.alloc(Term::Fn {
            functor: eq_named,
            pos_args: SmallVec::from_slice(&[one, one]),
            named_args: SmallVec::new(),
        });
        let rid = kb.assert_fact(head, ClauseKind::Fact, domain, None);
        assert!(
            !kb.is_equation(rid),
            "a bare `eq`-NAMED head is not the canonical equality connective"
        );
    }

    #[test]
    fn bootstrapped_kb_resolves_the_canonical_equality_head() {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);

        // The accessors return the QUALIFIED symbols, and `intern` of the short
        // name is a DIFFERENT symbol — the distinction the deleted fallback
        // erased, and the reason a bare `intern("eq")` found none of the loaded
        // `[simp]` equations.
        let eq = kb.eq_functor();
        assert_eq!(Some(eq), kb.try_resolve_symbol("anthill.prelude.PartialEq.eq"));
        assert_ne!(eq, kb.intern("eq"), "the qualified head and a bare `eq` must stay distinct");

        let unify = kb.unify_functor();
        assert_eq!(Some(unify), kb.try_resolve_symbol("anthill.kernel.unify"));
        assert_ne!(unify, kb.intern("unify"));
    }

    #[test]
    fn reify_value_chases_and_guards_var_bindings() {
        // WI-547: a bound bare `Value::Var` chases through σ (z → w → Int64(7));
        // a self-binding `s ↦ Value::Var(s)` (which `compose` can synthesize)
        // returns the var unchanged instead of recursing forever; an unbound var
        // passes through.
        use crate::eval::value::Value;
        use term::Var;
        let mut kb = KnowledgeBase::new();
        let (vz, vw, vs, vfree, seven) = {
            let z = kb.intern("z"); let vz = kb.fresh_var(z);
            let w = kb.intern("w"); let vw = kb.fresh_var(w);
            let s = kb.intern("s"); let vs = kb.fresh_var(s);
            let fr = kb.intern("free"); let vfree = kb.fresh_var(fr);
            let seven = kb.alloc(Term::Const(Literal::Int(7)));
            (vz, vw, vs, vfree, seven)
        };
        let mut subst = subst::Substitution::new();
        subst.bindings.insert(vz, Value::Var(Var::Global(vw)));   // z → w
        subst.bindings.insert(vw, Value::term(seven));            // w → 7
        subst.bindings.insert(vs, Value::Var(Var::Global(vs)));   // s → s (cycle)

        // z chases z → w → 7.
        match kb.reify_value(&Value::Var(Var::Global(vz)), &subst) {
            Value::Term { id: t, .. } => assert!(matches!(kb.get_term(t), Term::Const(Literal::Int(7)))),
            other => panic!("z should chase to Int64(7), got {other:?}"),
        }
        // Self-binding terminates and returns the var.
        match kb.reify_value(&Value::Var(Var::Global(vs)), &subst) {
            Value::Var(v) => assert_eq!(v.as_global(), Some(vs)),
            other => panic!("self-binding should pass through as the var, got {other:?}"),
        }
        // Unbound var passes through.
        match kb.reify_value(&Value::Var(Var::Global(vfree)), &subst) {
            Value::Var(v) => assert_eq!(v.as_global(), Some(vfree)),
            other => panic!("unbound var should pass through, got {other:?}"),
        }
    }

    #[test]
    fn reify_sigma_applies_a_node_binding_wi691() {
        // WI-691: a query var bound to a `Value::Node` carrying inner logic vars
        // must reify to the FULLY σ-applied answer. The former `reify` non-Term
        // arm returned the Node binding RAW (`other => other`), so the inner vars
        // stayed unresolved even though σ determined them — the gap the WI-690
        // unfold (which binds a query var to a Node pattern) first exposed. The
        // fix routes a non-Term binding through `reify_value`.
        use crate::eval::value::Value;
        use term::Var;
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("pair");
        let a_vid = { let n = kb.intern("a"); kb.fresh_var(n) };
        let v1 = { let n = kb.intern("v1"); kb.fresh_var(n) };
        let v2 = { let n = kb.intern("v2"); kb.fresh_var(n) };
        let a_term = kb.alloc(Term::Var(Var::Global(a_vid)));
        let one = kb.alloc(Term::Const(Literal::Int(1)));
        let two = kb.alloc(Term::Const(Literal::Int(2)));
        // A Node binding carrying inner logic vars: pair(?v1, ?v2) as a Value::Node.
        let v1t = kb.alloc(Term::Var(Var::Global(v1)));
        let v2t = kb.alloc(Term::Var(Var::Global(v2)));
        let inner = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_slice(&[v1t, v2t]),
            named_args: SmallVec::new(),
        });
        let node = node_occurrence::materialize_from_handle(&kb, inner);
        let mut subst = subst::Substitution::new();
        subst.bindings.insert(a_vid, Value::Node(node)); // ?a ↦ Node pair(?v1, ?v2)
        subst.bindings.insert(v1, Value::term(one)); // ?v1 ↦ 1
        subst.bindings.insert(v2, Value::term(two)); // ?v2 ↦ 2

        let val = kb.reify(a_term, &subst);
        // Lower whatever carrier the answer rides to its Term twin and check the
        // inner vars are resolved (before the fix these stayed `Var` leaves).
        let t = node_occurrence::value_to_term(&mut kb, &val).expect("answer lowers to a term");
        match kb.get_term(t).clone() {
            Term::Fn { functor, pos_args, .. } => {
                assert_eq!(functor, f, "functor preserved");
                assert!(
                    matches!(kb.get_term(pos_args[0]), Term::Const(Literal::Int(1))),
                    "?v1 must resolve to 1, got {:?}",
                    kb.get_term(pos_args[0]),
                );
                assert!(
                    matches!(kb.get_term(pos_args[1]), Term::Const(Literal::Int(2))),
                    "?v2 must resolve to 2, got {:?}",
                    kb.get_term(pos_args[1]),
                );
            }
            other => panic!("reify(?a) must be ground pair(1, 2), got {other:?}"),
        }
    }

    // WI-922: `assert_and_query_by_sort` lived here. Its whole subject was the
    // retired `by_sort` index (assert a fact, look it up by its sort key), so it
    // is deleted rather than ported — there is no replacement question to ask.
    // `assert_fact`'s surviving indexing is pinned by `value_fact_is_indexed_and_
    // queryable` (rules_by_functor + discrim) and `retract_removes_from_index`.
    // See the index-declaration comment for why no `rules_by_sort` replaces it.

    #[test]
    fn make_entity_term_orders_named_by_declared_field_not_interning() {
        // WI-299: `make_entity_term` must order named args by the functor's
        // DECLARED field order, not by `Symbol::index()` (interning order). We
        // intern the fields in the REVERSE of their declared order so the two
        // orders disagree; an ad-hoc `s.index()` sort would mis-order the term
        // and silently miss the loader-canonicalized pattern in the (positional)
        // discrimination matcher.
        let mut kb = KnowledgeBase::new();

        // Intern `second` BEFORE `first`, so index(second) < index(first) — the
        // OPPOSITE of the declared `[first, second]` order registered below.
        let second = kb.intern("second");
        let first = kb.intern("first");
        assert!(
            second.index() < first.index(),
            "test setup: interning order must invert declared order"
        );

        let functor = kb.intern("Pair");
        kb.register_entity_fields(functor, vec![first, second]);

        let v1 = kb.alloc(Term::Const(Literal::Int(1)));
        let v2 = kb.alloc(Term::Const(Literal::Int(2)));
        let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named.push((second, v2));
        named.push((first, v1));
        let term = kb.make_entity_term(functor, SmallVec::new(), named);

        match kb.terms.get(term) {
            Term::Fn { named_args, .. } => {
                let order: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
                assert_eq!(
                    order,
                    vec![first, second],
                    "named args must follow declared field order, not interning order"
                );
            }
            other => panic!("expected Term::Fn, got {other:?}"),
        }

        // With NO registered field list, `make_entity_term` falls back to
        // interning order (anonymous shape) — preserving prior behavior.
        let anon = kb.intern("Anon");
        let mut named2: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named2.push((first, v1));
        named2.push((second, v2));
        let anon_term = kb.make_entity_term(anon, SmallVec::new(), named2);
        match kb.terms.get(anon_term) {
            Term::Fn { named_args, .. } => {
                let order: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
                // `second` was interned first, so it sorts first under the fallback.
                assert_eq!(order, vec![second, first]);
            }
            other => panic!("expected Term::Fn, got {other:?}"),
        }
    }

    #[test]
    fn value_fact_node_head_indexes_queries_and_preserves_node_identity() {
        // WI-348 Phase B: a fact whose head carries a `Value::Node` (denoted)
        // is stored, indexed (rules_by_functor / discrim), queried back, and
        // — crucially — a variable query binds the SAME occurrence (Node identity
        // preserved through the answer via the carrier-faithful resolve).
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb); // interns Type.denoted etc. for occ_head
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let f_sym = kb.intern("op_with_denoted");
        let c_sym = kb.intern("c");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");

        // Head: f(denoted(value: Ref(c))) — the positional arg is a Node.
        let denoted_occ = kb.make_denoted_occ_ref(c_sym, span, None);
        let head = Value::Entity {
            functor: f_sym,
            pos: Rc::from(vec![Value::Node(Rc::clone(&denoted_occ))]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };

        let rid = kb.assert_fact_value(head, sort, domain, None);

        // Indexed by top-level functor (via the head's TermView).
        assert_eq!(kb.rules_by_functor(f_sym), vec![rid]);

        // Query f(?x): the value fact matches; ?x binds the Node by identity.
        let xv = kb.fresh_var(c_sym);
        let var_t = kb.alloc(Term::Var(Var::Global(xv)));
        let query = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_t, 1),
            named_args: SmallVec::new(),
        });
        let results = kb.query_view(&query);
        assert_eq!(results.len(), 1, "value fact should be found by f(?x)");
        assert_eq!(results[0].0, rid);
        match results[0].1.resolve_as_value(xv) {
            Some(Value::Node(occ)) => assert!(
                Rc::ptr_eq(&occ, &denoted_occ),
                "?x must bind the SAME occurrence — Node identity preserved",
            ),
            other => panic!("?x should bind a Value::Node, got {other:?}"),
        }

        // Retract removes it from the active indexes.
        kb.retract(rid);
        assert!(kb.rules_by_functor(f_sym).is_empty(), "retracted value fact left in rules_by_functor");
        assert!(kb.query_view(&query).is_empty(), "retracted value fact still queryable");
    }

    #[test]
    fn value_fact_named_node_args_resolve_by_key() {
        // WI-348 Phase B (review #4): a value head with NAMED args — one a Node,
        // one a ground term — resolves each query var to the child keyed by NAME
        // (not by position), and the Node arg keeps occurrence identity. Exercises
        // the carrier-faithful `extract_value_at_path` Named arm that the
        // positional-only happy-path test never touched.
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let f_sym = kb.intern("op_named");
        let c_sym = kb.intern("c");
        // `alpha` interned before `beta` → canonical (Symbol-index) order [alpha, beta].
        let alpha = kb.intern("alpha");
        let beta = kb.intern("beta");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");

        let denoted_occ = kb.make_denoted_occ_ref(c_sym, span, None);
        let beta_t = kb.alloc(Term::Const(Literal::Int(7)));
        let head = Value::Entity {
            functor: f_sym,
            pos: Rc::from(Vec::<Value>::new()),
            named: {
                let n: Vec<(Symbol, Value)> = vec![
                    (alpha, Value::Node(Rc::clone(&denoted_occ))),
                    (beta, Value::term(beta_t)),
                ];
                Rc::from(n)
            },
        };

        let rid = kb.assert_fact_value(head, sort, domain, None);

        // Query f(alpha: ?x, beta: ?y).
        let xv = kb.fresh_var(c_sym);
        let yv = kb.fresh_var(c_sym);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let yt = kb.alloc(Term::Var(Var::Global(yv)));
        let query = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(alpha, xt), (beta, yt)]),
        });
        let results = kb.query_view(&query);
        assert_eq!(results.len(), 1, "named-arg value fact should be found");
        assert_eq!(results[0].0, rid);

        // alpha → the Node (by key); beta → the Int term (by key).
        match results[0].1.resolve_as_value(xv) {
            Some(Value::Node(occ)) => assert!(
                Rc::ptr_eq(&occ, &denoted_occ),
                "alpha must bind the SAME occurrence",
            ),
            other => panic!("alpha should bind the Node, got {other:?}"),
        }
        assert_eq!(
            results[0].1.resolve_as_value(yv).map(|v| v.expect_term()),
            Some(beta_t),
            "beta must bind its ground term by key, not by position",
        );
    }

    #[test]
    fn value_fact_full_resolver_search_binds_node_as_value() {
        // WI-348: drive a value-fact head through the FULL SLD resolver
        // (`kb.resolve`, not just `kb.query` — so it exercises the resolver's
        // per-candidate triage, the path `is_equation` sits on) and confirm the
        // answer binds the query var to the Node *as a `Value`*, occurrence
        // identity intact. The substitution result is carrier-agnostic — a
        // `Value`, NOT a `TermId`: materializing the Node to a term would be lossy
        // and is never needed (consumers read the binding via `resolve_as_value`).
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let f_sym = kb.intern("vf");
        let c_sym = kb.intern("c");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");

        // Value fact: vf(Node(denoted(c))) — a Node-carrying head.
        let denoted_occ = kb.make_denoted_occ_ref(c_sym, span, None);
        let head = Value::Entity {
            functor: f_sym,
            pos: Rc::from(vec![Value::Node(Rc::clone(&denoted_occ))]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        kb.assert_fact_value(head, sort, domain, None);

        // SEARCH via the full resolver (not `kb.query`): vf(?x).
        let xv = kb.fresh_var(c_sym);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let goal = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(xt, 1),
            named_args: SmallVec::new(),
        });
        let config = resolve::ResolveConfig {
            max_solutions: 4,
            ..resolve::ResolveConfig::default()
        };
        let solutions = kb.resolve(&[goal], &config);
        assert_eq!(solutions.len(), 1, "the value fact must be found by the full resolver");

        // ?x binds the Node *as a Value*, identity preserved through the answer
        // substitution — the carrier-agnostic substitution result.
        match solutions[0].subst.resolve_as_value(xv) {
            Some(Value::Node(occ)) => assert!(
                Rc::ptr_eq(&occ, &denoted_occ),
                "?x must bind the SAME occurrence through the full resolver",
            ),
            other => panic!("?x should bind the Node through resolve, got {other:?}"),
        }

        // WI-348: `reify` is now carrier-agnostic — reading the answer binding
        // through it preserves the Node identity (the former `TermId`-only reify
        // SILENTLY dropped it, leaving `?x` unbound: this is the gap this test
        // now closes). The bare var reifies to the Node itself; the whole goal
        // `vf(?x)` reifies to a `Value::Entity` carrying that same Node in its
        // child slot (the `Fn`-with-a-non-`Term`-child carrier).
        let subst = solutions[0].subst.clone();
        match kb.reify(xt, &subst) {
            Value::Node(occ) => assert!(
                Rc::ptr_eq(&occ, &denoted_occ),
                "reify(?x) must yield the SAME occurrence, identity intact",
            ),
            other => panic!("reify(?x) should yield the Node, got {other:?}"),
        }
        match kb.reify(goal, &subst) {
            Value::Entity { functor, pos, named, .. } => {
                assert_eq!(functor, f_sym, "reify(vf(?x)) keeps the functor");
                assert!(named.is_empty(), "vf has no named args");
                match &pos[..] {
                    [Value::Node(occ)] => assert!(
                        Rc::ptr_eq(occ, &denoted_occ),
                        "reify(vf(?x)) must carry the SAME occurrence in its child slot",
                    ),
                    other => panic!("reify(vf(?x)) pos should be [Node], got {other:?}"),
                }
            }
            other => panic!("reify(vf(?x)) should be a Value::Entity, got {other:?}"),
        }
    }

    #[test]
    fn value_fact_dedup_keeps_distinct_node_answers() {
        // WI-348: the answer-dedup now keys on a carrier-agnostic structural
        // fingerprint (`goal_fingerprint`) instead of a materialized
        // `TermId`. Two solutions that bind the query var to
        // STRUCTURALLY-DISTINCT `Value::Node` answers must therefore stay
        // distinct — the former key dropped the Node to the bare var, collapsing
        // both to one key and silently losing a genuine answer.
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb); // interns the `denoted` field key `value`
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let f_sym = kb.intern("vf");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");

        // Two value facts with structurally-distinct Node heads:
        // vf(denoted(c1)), vf(denoted(c2)).
        for name in ["c1", "c2"] {
            let c = kb.intern(name);
            let occ = kb.make_denoted_occ_ref(c, span, None);
            let head = Value::Entity {
                functor: f_sym,
                pos: Rc::from(vec![Value::Node(occ)]),
                named: Rc::from(Vec::<(Symbol, Value)>::new()),
            };
            kb.assert_fact_value(head, sort, domain, None);
        }

        // Query vf(?x): both facts match, two distinct Node answers.
        let xv = kb.fresh_var(f_sym);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let goal = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(xt, 1),
            named_args: SmallVec::new(),
        });
        let config = resolve::ResolveConfig {
            max_solutions: 8,
            ..resolve::ResolveConfig::default()
        };
        let solutions = kb.resolve(&[goal], &config);

        // The dedup fingerprints the Node structure, so it keeps both — it does
        // NOT collapse them to one var key (the pre-WI-348 materialize-to-`TermId` bug).
        assert_eq!(solutions.len(), 2, "distinct Node answers must NOT be deduped to one");

        let nodes: Vec<_> = solutions
            .iter()
            .filter_map(|s| match s.subst.resolve_as_value(xv) {
                Some(Value::Node(occ)) => Some(Rc::clone(occ)),
                _ => None,
            })
            .collect();
        assert_eq!(nodes.len(), 2, "both answers bind ?x to a Node");
        assert!(
            !Rc::ptr_eq(&nodes[0], &nodes[1]),
            "the two Node answers are distinct occurrences, kept distinct by the structural key",
        );
    }

    #[test]
    fn wi472_node_head_fact_dedup() {
        // WI-472: two structurally-identical Node/Entity-headed ground facts must
        // dedup to ONE RuleEntry via the derived key — closing the WI-348
        // Node-head fact-dedup-miss (where both inserted). WI-815 changed WHAT that
        // key is (a `GoalKey` fingerprint, not a materialized `TermId`); this test
        // is unchanged, and is the port's control that dedup still happens.
        // Also checks a distinct structure stays distinct and assert/retract/
        // re-assert behaves.
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb); // interns the `denoted` field key `value`
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let f_sym = kb.intern("vf");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");

        // Build an Entity head `vf(denoted(c))`. The child occurrence is a FRESH
        // `Rc` each call (verified below), so two same-name heads are Rc-distinct
        // but structurally identical — the case that dedup must collapse.
        let entity_head = |kb: &mut KnowledgeBase, name: &str| {
            let c = kb.intern(name);
            let occ = kb.make_denoted_occ_ref(c, span, None);
            Value::Entity {
                functor: f_sym,
                pos: Rc::from(vec![Value::Node(occ)]),
                named: Rc::from(Vec::<(Symbol, Value)>::new()),
            }
        };

        // (1) Two identical Entity heads dedup to one RuleId (the fix): pre-WI-472
        //     this inserted two entries.
        let h1a = entity_head(&mut kb, "c1");
        let h1b = entity_head(&mut kb, "c1");
        if let (Value::Entity { pos: p1, .. }, Value::Entity { pos: p2, .. }) = (&h1a, &h1b) {
            if let (Value::Node(o1), Value::Node(o2)) = (&p1[0], &p2[0]) {
                assert!(!Rc::ptr_eq(o1, o2), "the two child occurrences are distinct Rc allocations");
            }
        }
        let r1 = kb.assert_fact_value(h1a, sort, domain, None);
        let r2 = kb.assert_fact_value(h1b, sort, domain, None);
        assert_eq!(r1, r2, "structurally-identical Entity heads must dedup to one RuleEntry");

        // (2) A structurally-distinct head gets its own RuleId (no over-dedup) —
        //     the invariant `value_fact_dedup_keeps_distinct_node_answers` guards
        //     at the query level, here at the RuleId level.
        let h2 = entity_head(&mut kb, "c2");
        let r3 = kb.assert_fact_value(h2, sort, domain, None);
        assert_ne!(r1, r3, "a structurally-distinct Entity head must NOT dedup");

        // (3) assert / retract / re-assert. After retract the dedup entry is removed
        //     (rid-guarded), so a re-assert of the same structure allocates a FRESH
        //     RuleId (mirrors the Term-head re-assert-after-retract behavior)…
        kb.retract(r1);
        let h3 = entity_head(&mut kb, "c1");
        let r4 = kb.assert_fact_value(h3, sort, domain, None);
        assert_ne!(r1, r4, "re-assert after retract allocates a fresh RuleEntry");
        // …and re-asserting that revived head once more dedups to it.
        let h4 = entity_head(&mut kb, "c1");
        let r5 = kb.assert_fact_value(h4, sort, domain, None);
        assert_eq!(r4, r5, "re-assert after revival dedups to the live RuleId");

        // (4) A BARE `Node` head (a `denoted(c)` directly, no Entity wrapper) dedups
        //     too — pre-WI-815 through `cached_term`'s per-occurrence memo, now
        //     through the same `GoalKey` walk the `Entity` arm uses.
        let c = kb.intern("bare");
        let n1 = Value::Node(kb.make_denoted_occ_ref(c, span, None));
        let n2 = Value::Node(kb.make_denoted_occ_ref(c, span, None));
        let sort2 = ClauseKind::Fact;
        let b1 = kb.assert_fact_value(n1, sort2, domain, None);
        let b2 = kb.assert_fact_value(n2, sort2, domain, None);
        assert_eq!(b1, b2, "structurally-identical bare Node heads dedup");
    }

    /// `functor(<n>)` as a value head, in the two shapes WI-815's lossy-key tests
    /// compare: `opaque = false` gives the head an `Int(n)` occurrence child,
    /// `opaque = true` gives it a `Value::OpRef` naming a per-`n` symbol — a
    /// NATIVE CARRIER, which views as the payload-free `ViewHead::Opaque`.
    ///
    /// ONE builder for both so the carrier swap is provably the ONLY difference
    /// between subject and control. Two hand-written fixtures could drift on
    /// functor arity, named args or child span, and the tests' whole claim is that
    /// nothing else differs.
    ///
    /// WI-1014 RE-POINTED THIS. The opaque subject used to be `Expr::SetLit`,
    /// which was opaque BY OMISSION — `occ_head` simply had no arm for it — and
    /// WI-1014 gave it one, so a set literal now decomposes and these two tests
    /// would have started failing at their central assert. That is the right
    /// failure mode and the wrong subject: a test about what happens to a
    /// payload-free key must not rest on a form that was only waiting for someone
    /// to write its arm.
    ///
    /// THE FIRST REPLACEMENT WAS `Value::OpRef`, AND IT WAS THE SAME MISTAKE —
    /// recorded rather than quietly swapped, because the reasoning is the point.
    /// It was justified as "a native carrier, not structural data, the same
    /// reason `Stream` / `Map` / `Cell` are". But an `OpRef` is not a handle: it
    /// is `{op: Symbol, dict, named}`, a PURE VALUE carrying a symbol. MEASURED:
    /// `views_structurally_equal` on one `OpRef` against ITSELF is `false`, and
    /// two `OpRef`s naming DIFFERENT ops share one `goal_fingerprint` — the exact
    /// pair of symptoms that made `SetLit` the wrong subject. It was opaque by
    /// omission too, and WI-1019 gave it a structural head, so it would ALSO have
    /// started failing here had it stayed the subject.
    ///
    /// `Value::FactRef` is the subject that actually qualifies, and the argument
    /// is the type's OWN CONTRACT rather than a claim about its carrier: it is a
    /// "KB-session-scoped locator" whose doc says it "never exposes a resident
    /// `RuleId`". A structural view would have to expose exactly what the type
    /// promises not to, so no future arm can decompose it without changing what
    /// `FactRef` IS. Two distinct rows are two distinct values a payload-free
    /// head cannot tell apart, which is the hazard these tests are about.
    ///
    /// WI-1019 CONFIRMED THAT CHOICE by asking the question generally: what a
    /// reference is spelled IN is what decides. An `OpRef` names its target with a
    /// `Symbol`, which has a `Value` carrier and means the same to every reader;
    /// a `FactRef` locates its row by a private slot index with no `Value` carrier
    /// at all. So this subject is opaque by NATURE, not by omission — the property
    /// these tests need and the one `SetLit` and `OpRef` both lacked.
    fn wi815_head(kb: &mut KnowledgeBase, functor: Symbol, n: i64, opaque: bool) -> crate::eval::value::Value {
        use crate::kb::node_occurrence::{Expr, NodeOccurrence};
        use crate::kb::term::Literal;
        use crate::span::{SourceId, SourceSpan};
        let child = if opaque {
            // Distinct row per `n`: the two subjects differ in a way that is REAL
            // and that an `Opaque` head cannot report — which is the hazard.
            crate::eval::value::Value::FactRef(crate::kb::extent::FactRef::resident(
                RuleId::from_raw(n as u32),
            ))
        } else {
            let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);
            crate::eval::value::Value::Node(NodeOccurrence::new_expr(
                Expr::Const(Literal::Int(n)),
                span,
                None,
            ))
        };
        crate::eval::value::Value::Entity {
            functor,
            pos: Rc::from(vec![child]),
            named: Rc::from(Vec::<(Symbol, crate::eval::value::Value)>::new()),
        }
    }

    /// A `FactRef` is an IDENTITY, not a shape: equal to itself, distinguishing
    /// two rows, and presenting no structure at all.
    ///
    /// WI-1019 REPLACED an `OpRef` test here. That one pinned WI-1014's stopgap,
    /// which existed because an `OpRef` measured as not equal to ITSELF — but the
    /// missing thing was a SHAPE, not an equality: an `OpRef` is two symbols and a
    /// dictionary, all three already `Value`-carried, so it now views structurally
    /// and never reaches the `(Opaque, Opaque)` arm. Its claims moved to
    /// `wi1019_native_carrier_view_test`, which needs a loaded KB to resolve the
    /// declared sort; a `FactRef` needs no symbols precisely BECAUSE it presents
    /// nothing, which is why this half stays a bare-KB unit test.
    ///
    /// The `FactRef` line the old test carried — "STILL not equal to itself" —
    /// was a pinned DEFECT. It is now a pinned property, and the difference is
    /// that `FactRef` is opaque BY NATURE rather than by omission: it locates its
    /// row by a private slot index (`RuleId` / `RowKey`) with no `Value` carrier,
    /// so there is nothing to present (proposal 005).
    ///
    /// CONTROL, MEASURED by deleting the `(Opaque, Opaque)` arm in
    /// `views_structurally_equal`: the equal-to-itself assert fails. The `!…`
    /// asserts pass either way BY DESIGN — without the arm everything is unequal
    /// — so only the positive case distinguishes the fix, and the negatives are
    /// what stop it from being "return true". The key assert fails if `Opaque`
    /// ever becomes payload-bearing, which is what would silently start deduping
    /// two distinct rows onto one key (WI-815).
    #[test]
    fn a_factref_is_an_identity_not_a_shape() {
        use crate::eval::value::Value;
        use term_view::{TermView, ViewHead};
        let kb = KnowledgeBase::new();
        let fr = |n: u32| Value::FactRef(crate::kb::extent::FactRef::resident(RuleId::from_raw(n)));

        assert!(
            matches!(fr(1).head(&kb), ViewHead::Opaque),
            "a FactRef presents no structure",
        );
        assert!(
            term_view::views_structurally_equal(&kb, &fr(1), &fr(1)),
            "a row reference is equal to itself",
        );
        assert!(
            !term_view::views_structurally_equal(&kb, &fr(1), &fr(2)),
            "and two distinct rows are not equal",
        );
        assert!(
            !term_view::goal_fingerprint(&kb, &fr(1), &crate::kb::subst::Substitution::new())
                .is_opaque_free(),
            "its key stays coarse, so fact dedup DECLINES it rather than merging \
             two rows — the coarseness is the safety, not a defect",
        );
    }

    /// WI-815 — A LOSSY KEY MUST DEGRADE TO NO DEDUP, NEVER COLLAPSE DISTINCT
    /// HEADS. Fact dedup drops the duplicate (returns the existing `RuleId`), so a
    /// key two DIFFERENT facts share does not merely lose precision — it silently
    /// discards one of them. This drives the guard at the key, which is where it
    /// lives; `wi815_an_opaque_bearing_head_cannot_be_stored_at_all` records why
    /// it cannot be driven one level up, at the fact.
    ///
    /// The subject is an `Opaque`-bearing head, so `f(setlit[1])` and
    /// `f(setlit[2])` produce the SAME `GoalKey`. That equality is ASSERTED below
    /// rather than assumed — it IS the hazard, and without it the test measures
    /// nothing.
    ///
    /// WHAT FAILS IF THE GUARD IS BACKED OUT — MEASURED, by deleting the
    /// `is_opaque_free()` filter from `value_fact_dedup_key` and re-running the
    /// workspace: this test fails (the key comes back `Some`, and the two heads
    /// then share it), and it is the ONLY one of 4140 that does. Nothing else drove the
    /// filter, which is why it is here — the same gap WI-1010's
    /// `an_unrunnable_own_member_is_not_a_supplier` was written to close.
    ///
    /// WHAT THIS IS A CONTROL FOR: the GUARD, not the port off `cached_term`. The
    /// port's controls are `wi472_node_head_fact_dedup` (dedup still happens, and
    /// part 3 here) and the compile itself.
    ///
    /// AND A CLAIM THIS COMMENT USED TO MAKE, WHICH WAS FALSE — corrected because it
    /// misdescribes the pre-change behaviour of this very fixture. It said an
    /// `Opaque`-bearing head "got no key before WI-815 either, because `value_to_term`
    /// returned `Err` on an opaque child". `value_to_term`'s `Value::Node` arm is
    /// `Ok(occurrence_to_term(..))` and cannot return `Err`; and WI-559 gave
    /// `Expr::SetLit` a real reifier, so this fixture's head had a VALID, injective
    /// key before the change and deduped correctly. After it, the head is `Opaque`
    /// and gets none. Both store two facts, so the test passes either way — but for
    /// opposite reasons, and "dedup behaviour unchanged, key for key" has this
    /// exception, which a hit-counting instrument could not see. WI-1014 re-points
    /// this fixture at a subject that is opaque BY NATURE.
    ///
    /// WHY THE GUARD IS THE WHOLE KEY AND NOT THE ROOT. The old check was
    /// `matches!(root, Term::Bottom)`, and it was asymmetric: for a BARE `Node`
    /// head `occ_build_fn` propagates a non-goal child with `?`, so the root really
    /// did become `Bottom` — but `value_to_term`'s `Value::Node` arm calls
    /// `occurrence_to_term`, which maps such a child to `Term::Bottom` WITHOUT
    /// propagating, so `Entity{f, [Node(<non-goal>)]}` lowered to `Fn{f, [Bottom]}`
    /// whose root is a `Fn` — and the guard passed it. Scanning the token sequence
    /// removes the asymmetry, and removes it in RELEASE, where the old path's
    /// `debug_assert!(false)` did nothing.
    #[test]
    fn wi815_a_lossy_key_degrades_to_no_dedup() {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        let f_sym = kb.intern("vf815");
        let domain = kb.intern("test");
        let kind = ClauseKind::Fact;

        // (1) THE HAZARD, asserted: two DISTINCT heads share one fingerprint,
        //     because the token standing for their differing child is payload-free.
        let sigma = subst::Substitution::new();
        let h1 = wi815_head(&mut kb, f_sym, 1, true);
        let h2 = wi815_head(&mut kb, f_sym, 2, true);
        let k1 = term_view::goal_fingerprint(&kb, &h1, &sigma);
        let k2 = term_view::goal_fingerprint(&kb, &h2, &sigma);
        assert_eq!(k1, k2, "an Opaque child erases the difference — this is the hazard");
        assert!(!k1.is_opaque_free(), "so the key is lossy and must not be used");

        // (2) THE GUARD: `value_fact_dedup_key` therefore answers `None` for both,
        //     which is what keeps the shared key from ever reaching the index.
        assert!(
            kb.value_fact_dedup_key(&h1).is_none() && kb.value_fact_dedup_key(&h2).is_none(),
            "a lossy key must degrade to no-dedup",
        );

        // (3) THE OTHER SIDE OF THE SAME RULE — the guard must not swallow heads it
        //     CAN key, and the port must still dedup. Same builder, `opaque = false`,
        //     so the SetLit wrapper is the only difference between (1)/(2) and this:
        //     an identical pair collapses to one entry and a distinct one does not,
        //     which is what makes "reject Opaque" different from "reject everything
        //     with a child". Without this, deleting the dedup entirely would satisfy
        //     (2) just as well.
        let g_sym = kb.intern("vg815");
        assert!(
            {
                let h = wi815_head(&mut kb, g_sym, 1, false);
                kb.value_fact_dedup_key(&h).is_some()
            },
            "the same head keys fine once its child is payload-bearing",
        );
        let hg1 = wi815_head(&mut kb, g_sym, 1, false);
        let hg1b = wi815_head(&mut kb, g_sym, 1, false);
        let hg2 = wi815_head(&mut kb, g_sym, 2, false);
        let p1 = kb.assert_fact_value(hg1, kind, domain, None);
        let p2 = kb.assert_fact_value(hg1b, kind, domain, None);
        let p3 = kb.assert_fact_value(hg2, kind, domain, None);
        assert_eq!(p1, p2, "identical keyable heads still dedup");
        assert_ne!(p1, p3, "and distinct ones still do not");
    }

    /// WI-815 — A NAMED TUPLE'S COMPONENT ORDER IS ITS IDENTITY, and the dedup key
    /// must not sort it away. REGRESSION TEST: WI-815 shipped this defect and a
    /// review caught it by DRIVING; it is fixed at `fingerprint_into`.
    ///
    /// The old key ran `value_to_term` -> `canonicalize_record_named_args`, which
    /// deliberately EXEMPTS an ORDERED PRODUCT (`is_ordered_product_functor`,
    /// i.e. `anthill.reflect.TupleLiteral`) because "a tuple's component source
    /// order IS its identity" (WI-788). `fingerprint_into` sorted unconditionally,
    /// so two DIFFERENT tuples produced ONE `GoalKey` — and fact dedup DROPS the
    /// duplicate, so the second tuple was silently discarded.
    ///
    /// WHAT FAILS IF THE FIX IS BACKED OUT — MEASURED, not predicted: remove the
    /// `ordered_product` guard from `fingerprint_into` and part (1) fails with both
    /// asserts (equal keys, and `assert_fact_value` returning the SAME RuleId for
    /// two distinct tuples). Remove the duplicate-label guard and part (2) fails
    /// the same way.
    ///
    /// WHY THE CORPUS DID NOT CATCH IT, recorded because the delivery claimed
    /// "dedup behaviour unchanged, key for key" on an instrument that could not see
    /// this: the instrumentation COUNTED keys and hits, and no `TupleLiteral`-headed
    /// value fact exists in the tree (0 of 103451). A hit count cannot detect a key
    /// that is wrong in a population of size zero — only driving the shape can.
    #[test]
    fn wi815_a_named_tuples_component_order_is_its_identity() {
        use crate::eval::value::Value;

        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        let tl = kb.resolve_symbol("anthill.reflect.TupleLiteral");
        let domain = kb.intern("test");
        let kind = ClauseKind::Fact;
        let sigma = subst::Substitution::new();
        let lit = |kb: &mut KnowledgeBase, n: i64| {
            Value::Term { id: kb.alloc(Term::Const(crate::kb::term::Literal::Int(n))) }
        };

        // (1) ORDER. `(x: 1, y: 2)` and `(y: 2, x: 1)` are two different tuples.
        let (x, y) = (kb.intern("xcomp"), kb.intern("ycomp"));
        let (one, two) = (lit(&mut kb, 1), lit(&mut kb, 2));
        let tuple = |named: Vec<(Symbol, Value)>| Value::Entity {
            functor: tl,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(named),
        };
        let h1 = tuple(vec![(x, one.clone()), (y, two.clone())]);
        let h2 = tuple(vec![(y, two.clone()), (x, one.clone())]);
        assert_ne!(
            term_view::goal_fingerprint(&kb, &h1, &sigma),
            term_view::goal_fingerprint(&kb, &h2, &sigma),
            "component order is identity for an ordered product — the keys must differ",
        );
        let r1 = kb.assert_fact_value(h1, kind, domain, None);
        let r2 = kb.assert_fact_value(h2, kind, domain, None);
        assert_ne!(r1, r2, "two distinct tuples must stay TWO facts, not one");

        // …while a NON-ordered-product functor still sorts, so the two carriers of
        // one record agree. This is the control that the guard is scoped to ordered
        // products and did not simply disable sorting.
        let rec = kb.intern("wi815rec");
        let a = Value::Entity {
            functor: rec,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(x, one.clone()), (y, two.clone())]),
        };
        let b = Value::Entity {
            functor: rec,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(y, two.clone()), (x, one.clone())]),
        };
        assert_eq!(
            term_view::goal_fingerprint(&kb, &a, &sigma),
            term_view::goal_fingerprint(&kb, &b, &sigma),
            "an ordinary record still canonicalizes, so field order is NOT identity",
        );

        // (2) DUPLICATE LABEL. `named_arg` resolves by symbol and returns the FIRST
        //     match, so a repeated label makes the second component unreadable. The
        //     key must degrade rather than conflate; producers refuse duplicates
        //     (WI-805/808/809), but this primitive must not rely on that.
        let d = kb.intern("dupx");
        let three = lit(&mut kb, 3);
        let g1 = tuple(vec![(d, one.clone()), (d, two.clone())]);
        let g2 = tuple(vec![(d, one.clone()), (d, three.clone())]);
        let kg1 = term_view::goal_fingerprint(&kb, &g1, &sigma);
        assert!(!kg1.is_opaque_free(), "a repeated label makes the key unusable");
        let q1 = kb.assert_fact_value(g1, kind, domain, None);
        let q2 = kb.assert_fact_value(g2, kind, domain, None);
        assert_ne!(q1, q2, "duplicate-label heads must not collapse into one fact");

        // (3) ANONYMOUS FUNCTOR. `Value::Unit` and an EMPTY `Value::Tuple` both head
        //     as `Functor{None, 0, 0}` and key as one payload-BEARING token
        //     `Open(None, 0, 0)` — so `is_opaque_free` cannot see the collision, and
        //     the old key refused them outright (`value_to_term` returned `Err` for
        //     `Unit` / `Tuple`). Dedup must not start admitting what its predecessor
        //     rejected. Backing out `has_named_functors` fails this arm.
        let unit_key = term_view::goal_fingerprint(&kb, &Value::Unit, &sigma);
        let empty_tuple = Value::Tuple {
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        assert_eq!(
            unit_key,
            term_view::goal_fingerprint(&kb, &empty_tuple, &sigma),
            "Unit and an empty Tuple are indistinguishable through the view — the hazard",
        );
        assert!(unit_key.is_opaque_free(), "and opaque-freedom cannot see it");
        assert!(
            kb.value_fact_dedup_key(&Value::Unit).is_none()
                && kb.value_fact_dedup_key(&empty_tuple).is_none(),
            "so an anonymous functor must get no dedup key",
        );
    }

    /// WI-815 — A HEAD THAT PROMISES N NAMED CHILDREN AND SUPPLIES FEWER MUST NOT
    /// KEY. The named twin of `pos_arg`'s `None` guard, driven on the live case.
    ///
    /// `type_node_head` returns a HARDCODED `named_arity` per form (`ExprCarried`
    /// → 2, `Arrow` → 4), while `type_node_keys` is
    /// `short_keys.iter().filter_map(|k| kb.lookup_symbol(k))` — it comes up SHORT
    /// whenever one of those names is not interned. That is not hypothetical: it is
    /// the state of an ORDINARY `register_prelude` KB, MEASURED — the qualified
    /// `anthill.prelude.TypeExtractor.ExprCarried` resolves (so the head really does
    /// announce arity 2) and `value` is interned, but `member` is NOT. So the key
    /// list holds ONE key for a head promising TWO, and two `ExprCarried` types
    /// differing only in `member` fingerprinted IDENTICALLY with nothing marking the
    /// loss — and the same head keys differently before and after that name is
    /// interned, making identity LOAD-ORDER-DEPENDENT.
    ///
    /// WHAT FAILS IF BACKED OUT — MEASURED, by deleting the
    /// `keys.len() != named_arity` guard and re-running: the `is_opaque_free` assert
    /// fails, because the short key list then yields a perfectly usable key for two
    /// types the view cannot tell apart, and fact dedup would drop one of them.
    ///
    /// Found by `/code-review` on the WI-815 follow-up, in the same family as the
    /// ordered-product and duplicate-label holes.
    #[test]
    fn wi815_a_short_named_key_list_cannot_key() {
        use crate::eval::value::Value;
        use crate::kb::node_occurrence::{NodeOccurrence, TypeChild, TypeNode};
        use crate::span::{SourceId, SourceSpan};

        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 4);

        // THE PRECONDITION, asserted rather than assumed — this test measures
        // nothing if the KB happens to intern both names.
        assert!(
            kb.try_resolve_symbol("anthill.prelude.TypeExtractor.ExprCarried").is_some(),
            "the head must really announce a functor with arity 2",
        );
        assert!(kb.lookup_symbol("value").is_some(), "`value` is interned");
        assert!(
            kb.lookup_symbol("member").is_none(),
            "`member` is NOT — this asymmetry is the whole subject",
        );

        let carried = |kb: &mut KnowledgeBase, member: &str| {
            let v = kb.intern("shared_value");
            let m = kb.intern(member);
            Value::Node(NodeOccurrence::new_type(
                TypeNode::ExprCarried {
                    value: TypeChild::Ground(kb.alloc(Term::Ident(v))),
                    member: TypeChild::Ground(kb.alloc(Term::Ident(m))),
                },
                span,
                None,
            ))
        };
        let a = carried(&mut kb, "alpha_member");
        let b = carried(&mut kb, "beta_member");
        let sigma = subst::Substitution::new();
        let ka = term_view::goal_fingerprint(&kb, &a, &sigma);

        // THE HAZARD: the view cannot distinguish them, because the key it names
        // `member` by was never emitted.
        assert_eq!(
            ka,
            term_view::goal_fingerprint(&kb, &b, &sigma),
            "differing only in `member`, these share one key — the hazard",
        );
        // THE GUARD: so the key must not be usable.
        assert!(
            !ka.is_opaque_free(),
            "a head promising more named children than the view supplies must degrade",
        );
        assert!(kb.value_fact_dedup_key(&a).is_none(), "and fact dedup must refuse it");
    }

    /// WI-815 — ONE OCCURRENCE, THREE CARRIERS, ONE KEY. A `Spliced` leaf carries a
    /// `Value`, and every `TermView` impl that can reach an occurrence must view
    /// through to it.
    ///
    /// `occ_head` delegates to the carried value internally, so the HEAD announced
    /// the value's functor and arity from every carrier. The CHILD readers did not:
    /// only the `Rc<NodeOccurrence>` impl checked `spliced_value`, while
    /// `Value::Node(occ)` and `ViewItem::Node(occ)` went straight to the `occ_*`
    /// helpers — which return OCCURRENCE children, and a `Spliced` leaf has none. So
    /// one occurrence answered differently depending on which carrier reached it: a
    /// head promising one child, and no child supplied.
    ///
    /// That is the WI-425 cross-carrier miss — a WRONG ANSWER, not a precision loss
    /// — and WI-815 made it load-bearing by keying fact dedup on the same walk.
    /// Found by `/code-review`; fixed by moving the delegation into shared
    /// `occ_view_*` owners all three impls call, so a carrier cannot forget.
    ///
    /// WHAT FAILS IF BACKED OUT — MEASURED: revert `Value::Node`'s arms to the bare
    /// `occ_*` helpers and part (1) fails (the two carriers disagree) and part (2)
    /// fails (two distinct spliced values collapse to one key).
    #[test]
    fn wi815_a_spliced_occurrence_keys_the_same_through_every_carrier() {
        use crate::eval::value::Value;
        use crate::kb::node_occurrence::{Expr, NodeOccurrence};
        use crate::span::{SourceId, SourceSpan};

        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 4);
        let g = kb.intern("wi815spliced");
        let sigma = subst::Substitution::new();

        let spliced = |kb: &mut KnowledgeBase, n: i64| {
            let lit = kb.alloc(Term::Const(crate::kb::term::Literal::Int(n)));
            let carried = Value::Entity {
                functor: g,
                pos: Rc::from(vec![Value::Term { id: lit }]),
                named: Rc::from(Vec::<(Symbol, Value)>::new()),
            };
            NodeOccurrence::new_expr(Expr::Spliced(carried), span, None)
        };
        let o1 = spliced(&mut kb, 1);
        let o2 = spliced(&mut kb, 2);

        // (1) THE SAME occurrence, read through the occurrence carrier and through
        //     `Value::Node`, must produce the SAME key.
        let via_occ = term_view::goal_fingerprint(&kb, &o1, &sigma);
        let via_value = term_view::goal_fingerprint(&kb, &Value::Node(Rc::clone(&o1)), &sigma);
        assert_eq!(
            via_occ, via_value,
            "an occurrence must key identically whichever carrier reaches it (WI-425)",
        );

        // (2) …and the key must still SEE the carried value, so two different
        //     splices stay different. Without the delegation both keyed as a bare
        //     head with no children.
        assert_ne!(
            via_value,
            term_view::goal_fingerprint(&kb, &Value::Node(Rc::clone(&o2)), &sigma),
            "distinct carried values must not collapse to one key",
        );

        // (3) and the key is usable — the delegation supplies the child the head
        //     promised, so the arity guard does not have to degrade it.
        assert!(
            via_value.is_opaque_free(),
            "a spliced occurrence with its child supplied keys cleanly",
        );
    }

    /// A `Value::SymbolRef` is INDISTINGUISHABLE from its `Term::Ref` twin —
    /// the whole claim the variant rests on, driven at each level that could
    /// disagree rather than asserted.
    ///
    /// CONTROL — which assertion fails when which piece is backed out, MEASURED
    /// by removing each:
    ///  - (1) fails if `Value::head`'s `SymbolRef` arm goes (it falls to the
    ///    `Opaque` group): the query stops matching a fact it must match, 0
    ///    solutions instead of 1. This is the assertion that would also catch a
    ///    future `functor_view_head` detour re-spelling the head.
    ///  - (2) fails if `value_symbol` is reverted to the `carrier_term` +
    ///    `Term::Ref | Term::Ident` match it replaced — that route is `None` for
    ///    every carrier but `Term`/`Node`, so it answers "not a symbol".
    ///  - (3) fails if `alloc_from_value`'s arm goes (`UnsupportedVariant`).
    ///  - (4) passes either way BY DESIGN. It pins that the OLD carrier still
    ///    answers, which is what makes (1)/(2) cross-carrier AGREEMENT claims
    ///    rather than a swap — without it, deleting the `Term` support entirely
    ///    would leave this test green.
    #[test]
    fn a_symbol_ref_value_is_indistinguishable_from_its_term_twin() {
        use crate::eval::value::Value;

        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        let p = kb.intern("symref_p");
        let foo = kb.intern("symref_foo");
        let bar = kb.intern("symref_bar");
        let domain = kb.intern("test");

        // The fact is stored the CLASSICAL way: a hash-consed `p(Ref(foo))`.
        // Nothing about the storage side knows the new carrier exists.
        let foo_ref = kb.alloc(Term::Ref(foo));
        let head = kb.alloc(Term::Fn {
            functor: p,
            pos_args: SmallVec::from_elem(foo_ref, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact_value(Value::Term { id: head }, ClauseKind::Fact, domain, None);

        let config = resolve::ResolveConfig::default();
        let query = |sym: Symbol| {
            Value::Entity {
                functor: p,
                pos: Rc::from(vec![Value::SymbolRef(sym)]),
                named: Rc::from(Vec::<(Symbol, Value)>::new()),
            }
        };

        // (1) A goal carrying the symbol as `Value::SymbolRef` MATCHES the fact
        //     that stored it as `Term::Ref` — through the discrimination tree,
        //     which is where a head-spelling disagreement would surface.
        assert_eq!(
            kb.resolve_goals(vec![query(foo)], &config).len(),
            1,
            "a SymbolRef goal must match its own Term::Ref twin in the index",
        );
        // …and the match is on the SYMBOL, not on "any symbol": a different one
        // must not match, or (1) would pass for a carrier that keys nothing.
        assert_eq!(
            kb.resolve_goals(vec![query(bar)], &config).len(),
            0,
            "a different symbol must not match — (1) must be discriminating",
        );

        // (2) The by-content reader answers the same symbol off either carrier.
        assert_eq!(kb.value_symbol(&Value::SymbolRef(foo)), Some(foo));
        assert_eq!(
            kb.value_symbol(&Value::SymbolRef(foo)),
            kb.value_symbol(&Value::Term { id: foo_ref }),
            "one symbol, one answer, whichever carrier is asked",
        );

        // (3) …and it lowers back to exactly that `TermId` — hash-consing makes
        //     this an identity check, not a structural one.
        assert_eq!(
            kb.alloc_from_value(&Value::SymbolRef(foo)).expect("SymbolRef lowers"),
            foo_ref,
            "the round-trip is lossless: SymbolRef(s) → Term::Ref(s)",
        );

        // (4) The interned carrier still works — see the CONTROL note.
        let term_query = Value::Entity {
            functor: p,
            pos: Rc::from(vec![Value::Term { id: foo_ref }]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        assert_eq!(
            kb.resolve_goals(vec![term_query], &config).len(),
            1,
            "the pre-existing carrier is untouched",
        );
    }

    /// WI-815 — THE TWO DEDUP KEY SPACES ARE DISJOINT, and that is a decision.
    ///
    /// `fact_dedup` keys a `Value::Term` head on its hash-consed `TermId`;
    /// `value_fact_dedup` keys a `Node`/`Entity` head on its `GoalKey`. Nothing
    /// bridges them, so a `Term` head and a structurally-identical value head are
    /// TWO facts. Pre-WI-815 they were one: the value key was materialized into a
    /// `TermId` and landed in the same map.
    ///
    /// Measured to cost nothing (zero cross-carrier dedup hits corpus-wide — see
    /// `docs/design/value-facts-carrier-agnostic-resolver.md` §Delivered), but a
    /// measurement of one moment is not a guard. The direction of travel in this
    /// subsystem (WI-348 / WI-621) is moving producers from `Term` heads to value
    /// heads, so a producer could one day flip a fact's carrier and silently stop
    /// deduping against its twin. This test is what makes that visible: it fails
    /// if someone unifies the key spaces, and its EXISTENCE is the record that the
    /// asymmetry is intended rather than an oversight.
    ///
    /// Sound in the only direction that matters: a split can lose a dedup (the
    /// duplicate is stored) but can never collapse two distinct facts into one.
    #[test]
    fn wi815_the_two_key_spaces_are_disjoint() {
        use crate::eval::value::Value;

        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        let f = kb.intern("vf815disjoint");
        let domain = kb.intern("test");
        let kind = ClauseKind::Fact;

        // `f(1)` twice over: once all-ground (a hash-consed `Term` head), once with
        // the same child carried as an occurrence (an `Entity` head).
        let one = kb.alloc(Term::Const(crate::kb::term::Literal::Int(1)));
        let term_head = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_elem(one, 1),
            named_args: SmallVec::new(),
        });
        let value_head = wi815_head(&mut kb, f, 1, false);

        let r_term = kb.assert_fact_value(Value::Term { id: term_head }, kind, domain, None);
        let r_value = kb.assert_fact_value(value_head, kind, domain, None);
        assert_ne!(
            r_term, r_value,
            "the carriers key different spaces, so this is TWO facts — if this ever \
             becomes one, the key spaces were unified and that is a semantic change",
        );

        // …and each still dedups WITHIN its own space, so the split is a split and
        // not a broken index.
        let r_term2 = kb.assert_fact_value(Value::Term { id: term_head }, kind, domain, None);
        let vh2 = wi815_head(&mut kb, f, 1, false);
        let r_value2 = kb.assert_fact_value(vh2, kind, domain, None);
        assert_eq!(r_term, r_term2, "Term heads still dedup among themselves");
        assert_eq!(r_value, r_value2, "value heads still dedup among themselves");
    }

    /// WI-815 — WHY THE LOSSY-KEY GUARD CANNOT BE DRIVEN AT THE FACT LEVEL, pinned
    /// rather than asserted in prose.
    ///
    /// The ticket asked for a test that two structurally-distinct `Opaque`-bearing
    /// heads "stay separate facts". They cannot be facts at all: `assert_fact_value`
    /// stores through `push_value_head_entry`, whose discrimination-tree insert
    /// walks EVERY positional and named child (`insert_walk_args`) and PANICS on an
    /// `Opaque` head — a deliberate loud refusal that predates WI-815 ("no fact/rule
    /// form in use today produces a functor-less / opaque stored head; fail loudly
    /// rather than silently mis-index"). So the refusal that actually fires is
    /// louder than the dedup guard — though NOT earlier: `assert_fact_value` calls
    /// `value_fact_dedup_key` first and only then `push_value_head_entry`, so the
    /// guard runs and degrades, and the panic follows for the same head. (An earlier
    /// draft of this comment claimed the panic came first. That is the reasoning
    /// which would retire the guard as unreachable, so it is corrected rather than
    /// quietly dropped.)
    ///
    /// That makes `is_opaque_free()` defence-in-depth, and it stays for a reason the
    /// panic does not cover: the two failure modes are not equivalent. The discrim
    /// panic is loud; a lossy dedup key silently DROPS a fact. If a future carrier
    /// or a widened discrim keying makes such a head storable, the dedup path must
    /// already be correct — it must not be the thing that has to be remembered.
    ///
    /// This test also bounds the claim: it will start failing the moment such a
    /// head becomes storable, which is exactly when
    /// `wi815_a_lossy_key_degrades_to_no_dedup` should grow its fact-level half.
    #[test]
    #[should_panic(expected = "functor-less / opaque head")]
    fn wi815_an_opaque_bearing_head_cannot_be_stored_at_all() {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        let f_sym = kb.intern("vf815panic");
        let domain = kb.intern("test");
        let head = wi815_head(&mut kb, f_sym, 1, true);
        kb.assert_fact_value(head, ClauseKind::Fact, domain, None);
    }

    /// WI-922: this was `entity_of_query_includes_children`, and its first half
    /// asserted the retired `by_sort` index's one-level entity-child union —
    /// `by_sort(Nat)` returning a fact filed under the CONSTRUCTOR `zero`.
    ///
    /// That union was already dead in production and this test was its only
    /// cover, because it manufactured its own subject: nothing files a clause
    /// under a constructor symbol. The one path that keys on a declared sort is
    /// `assert_checked_persistent` -> [`Self::fact_trigger_sort`] ->
    /// `view_to_trigger_sort`, which returns `strict_parent_sort(functor)`
    /// — the PARENT, never the child. So the union could only ever fire on a
    /// key a test wrote by hand. Deleted with the index; the `is_entity_of`
    /// half, which is about the entity registry and not the clause index,
    /// survives here.
    #[test]
    fn register_entity_of_is_readable_by_is_entity_of() {
        let mut kb = KnowledgeBase::new();
        let nat = kb.make_name_term("Nat");
        let zero = kb.make_name_term("zero");

        let nat_sym = kb.name_term_sym(nat);
        kb.register_sort(nat_sym, SortKind::Sort);
        kb.register_entity_of(zero, nat);

        // is_entity_of (the TermId-ergonomic wrapper over the carrier-neutral core)
        assert!(kb.is_entity_of(zero, nat));
        assert!(!kb.is_entity_of(nat, zero));
    }

    /// WI-697 — `is_entity_of` reads its operands through `TermView` (no reify),
    /// keys the parent index by the constructor SYMBOL (retiring the Fn/Ref
    /// dual-keying), and keeps the reflexive check STRUCTURAL (not symbol-eq).
    #[test]
    fn is_entity_of_is_carrier_neutral() {
        use crate::eval::value::Value;
        let mut kb = KnowledgeBase::new();
        let nat = kb.make_name_term("Nat");
        let zero = kb.make_name_term("zero"); // Fn{zero} — succ not yet a constructor
        kb.register_sort(kb.name_term_sym(nat), SortKind::Sort);
        kb.register_entity_of(zero, nat);

        // Term carriers via the ergonomic wrapper — reflexive / positive / negative.
        assert!(kb.is_entity_of(nat, nat), "reflexive");
        assert!(kb.is_entity_of(zero, nat), "zero ⊳ Nat");
        assert!(!kb.is_entity_of(nat, zero), "Nat ⋫ zero");

        // Carrier-neutral core: a `Value::Node` operand resolves with NO reification
        // — the whole point of WI-697.
        let zero_node = Value::Node(crate::kb::node_occurrence::materialize_from_handle(&kb, zero));
        let nat_node = Value::Node(crate::kb::node_occurrence::materialize_from_handle(&kb, nat));
        assert!(kb.is_entity_of_view(&zero_node, &Value::term(nat)), "Node sub ⊳ Term sup");
        assert!(kb.is_entity_of_view(&zero_node, &nat_node), "Node sub ⊳ Node sup");
        assert!(!kb.is_entity_of_view(&nat_node, &zero_node), "Node Nat ⋫ Node zero");

        // Cross-spelling: register `succ` as the pre-canon `Fn{succ}`; a post-canon
        // `Ref(succ)` (WI-511 alloc canon, gated on is_constructor_symbol) query
        // resolves via the SINGLE symbol key — what the TermId dual-keying did before.
        let succ_fn = kb.make_name_term("succ"); // Fn{succ} (succ not a ctor yet)
        kb.register_entity_of(succ_fn, nat); // now succ IS a constructor
        let succ_ref = kb.make_name_term("succ"); // alloc canonicalizes Fn{succ} → Ref(succ)
        assert_ne!(succ_fn, succ_ref, "the two spellings must be distinct TermIds");
        assert!(kb.is_entity_of(succ_fn, nat), "Fn{{succ}} spelling");
        assert!(kb.is_entity_of(succ_ref, nat), "Ref(succ) spelling");

        // Reflexive is STRUCTURAL, not symbol-eq: same head, different args ⇒ NOT
        // equal (symbol-eq would wrongly conflate them — the List[Int]/List[Str] case).
        let box_sym = kb.intern("box");
        let box_zero = kb.alloc(term::Term::Fn {
            functor: box_sym,
            pos_args: smallvec::SmallVec::from_elem(zero, 1),
            named_args: smallvec::SmallVec::new(),
        });
        let box_nat = kb.alloc(term::Term::Fn {
            functor: box_sym,
            pos_args: smallvec::SmallVec::from_elem(nat, 1),
            named_args: smallvec::SmallVec::new(),
        });
        assert!(kb.is_entity_of(box_zero, box_zero), "structurally identical");
        assert!(!kb.is_entity_of(box_zero, box_nat), "same head, diff args ⇒ not equal");

        // Nullary gate: an APPLIED constructor `succ(zero)` is NOT an entity of its
        // sort — the parent lookup fires only for a bare constructor identity, as
        // the pre-WI-697 TermId-keyed index (nullary keys only) did.
        let succ_sym = kb.intern("succ");
        let succ_applied = kb.alloc(term::Term::Fn {
            functor: succ_sym,
            pos_args: smallvec::SmallVec::from_elem(zero, 1),
            named_args: smallvec::SmallVec::new(),
        });
        assert!(!kb.is_entity_of(succ_applied, nat), "applied succ(zero) ⋫ Nat (nullary-gated)");
    }

    #[test]
    fn value_rule_head_node_stored_and_read_back() {
        // WI-373 slice 1: the carrier-agnostic storage epilogue `assert_rule_nodes`
        // (converged with `assert_fact_value`) stores a RULE head — with a body,
        // not just a fact — that carries a `Value::Node` denoted occurrence, and
        // `rule_head_value` reads it back with the occurrence identity intact.
        // (DeBruijn-*closing* a denoted head is gated on WI-342 P3 — the
        // Type-occurrence var-walk — so this exercises the no-var storage path.)
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let vf = kb.intern("vf");
        let cond = kb.intern("cond");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");

        // Head vf(denoted(c1)) — a ground Value::Entity carrying a Node child.
        let c1 = kb.intern("c1");
        let denoted = kb.make_denoted_occ_ref(c1, span, None);
        let head = Value::Entity {
            functor: vf,
            pos: Rc::from(vec![Value::Node(Rc::clone(&denoted))]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };

        // A ground body atom, so this is a rule (non-empty body), not a fact.
        let cond_goal = kb.alloc(Term::Fn {
            functor: cond,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[cond_goal]);

        let rid = kb.assert_rule_nodes(head, body_nodes, sort, domain, None);

        match kb.rule_head_value(rid) {
            Value::Entity { functor, pos, .. } => {
                assert_eq!(*functor, vf);
                match &pos[0] {
                    Value::Node(occ) => assert!(
                        Rc::ptr_eq(occ, &denoted),
                        "the denoted occurrence must survive storage with identity intact",
                    ),
                    other => panic!("head child should be the Node, got {other:?}"),
                }
            }
            other => panic!("value rule head should be a Value::Entity, got {other:?}"),
        }
    }

    #[test]
    fn value_head_debruijn_var_in_occurrence_indexes_like_term() {
        // WI-373: a De Bruijn var carried INSIDE an occurrence value head now
        // keys a var-edge in the discrimination tree, the same as a term head's
        // De Bruijn var — `occ_index_var` surfaces `Expr::Var` of any kind,
        // mirroring `TermIdView`'s `Term::Var(v) => Some(v)`. Before this fix the
        // insert read `Opaque` and panicked ("value-fact keying unimplemented").
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);

        let vf = kb.intern("vf");
        let g = kb.intern("g");
        let cond = kb.intern("cond");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");

        // An occurrence `g(DeBruijn(0))` — the shape a stored value rule head's
        // child takes after De Bruijn closure.
        let xv = kb.fresh_var(vf);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let g_term = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(xt, 1),
            named_args: SmallVec::new(),
        });
        let g_global = node_occurrence::materialize_from_handle(&kb, g_term);
        let g_db = node_occurrence::node_to_debruijn(&mut kb, &g_global, &[xv]);

        let head = Value::Entity {
            functor: vf,
            pos: Rc::from(vec![Value::Node(g_db)]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        let cond_goal = kb.alloc(Term::Fn {
            functor: cond,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[cond_goal]);

        // Indexes without panicking (the De Bruijn var routes to a var-edge)...
        let rid = kb.assert_rule_nodes(head, body_nodes, sort, domain, None);

        // ...and the head is discoverable by a query on its functor.
        let yv = kb.fresh_var(vf);
        let yt = kb.alloc(Term::Var(Var::Global(yv)));
        let query = kb.alloc(Term::Fn {
            functor: vf,
            pos_args: SmallVec::from_elem(yt, 1),
            named_args: SmallVec::new(),
        });
        let found = kb.query_view(&query);
        assert!(
            found.iter().any(|(r, _)| *r == rid),
            "the De Bruijn-bearing value head must be indexed + queryable",
        );
    }

    #[test]
    fn value_rule_head_with_var_asserts_closes_and_indexes() {
        // WI-373: a var-bearing value rule head asserts via the carrier-agnostic
        // De Bruijn path — `collect_value_head_vars` finds the var inside the Expr
        // Node child (arity 1), `close_value_head_debruijn` closes it, and gap-2
        // discrim keying indexes it (queryable). RESOLVING such a head is loudly
        // gated on the binding-extraction half of gap 3 (see `with_fresh_vars`).
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);

        let vf = kb.intern("vf");
        let g = kb.intern("g");
        let thing = kb.intern("thing");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");

        // Head vf(g(?x)) — g(?x) carried as an Expr Node; body thing(?x).
        let xv = kb.fresh_var(vf);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let g_x = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(xt, 1),
            named_args: SmallVec::new(),
        });
        let g_occ = node_occurrence::materialize_from_handle(&kb, g_x);
        let head = Value::Entity {
            functor: vf,
            pos: Rc::from(vec![Value::Node(g_occ)]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        let thing_x = kb.alloc(Term::Fn {
            functor: thing,
            pos_args: SmallVec::from_elem(xt, 1),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[thing_x]);

        // Closure: collect the var inside the Node + close to De Bruijn + index.
        let rid = kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);
        assert_eq!(kb.rule_arity(rid), 1, "?x inside the Node is the rule's one var");

        // Discoverable by a query on its functor (gap-2 keying).
        let yv = kb.fresh_var(vf);
        let yt = kb.alloc(Term::Var(Var::Global(yv)));
        let g_y = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(yt, 1),
            named_args: SmallVec::new(),
        });
        let query = kb.alloc(Term::Fn {
            functor: vf,
            pos_args: SmallVec::from_elem(g_y, 1),
            named_args: SmallVec::new(),
        });
        assert!(
            kb.query_view(&query).iter().any(|(r, _)| *r == rid),
            "the var-bearing value rule head must be indexed + queryable",
        );
    }

    #[test]
    fn value_rule_head_with_var_resolves_and_binds_nested() {
        // WI-373 gap 3 (binding extraction): RESOLVE against a var-bearing value
        // rule head. Rule  vf(g(?x)) :- thing(?x)  with head carried as a
        // Value::Node, plus fact thing("active"). A query vf(g(?y)) must bind the
        // NESTED ?y to the rule's head var, run the body, and answer ?y="active".
        // Before the nested binding-extraction this yielded an empty tree_subst
        // (?y unconstrained — a silent wrong answer) and `with_fresh_vars`
        // loud-guarded the value head; now it resolves carrier-faithfully.
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::kb::resolve::ResolveConfig;
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);

        let vf = kb.intern("vf");
        let g = kb.intern("g");
        let thing = kb.intern("thing");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");

        // Fact thing("active").
        let active = kb.alloc(Term::Const(Literal::String("active".into())));
        let thing_active = kb.alloc(Term::Fn {
            functor: thing, pos_args: SmallVec::from_elem(active, 1), named_args: SmallVec::new(),
        });
        kb.assert_fact(thing_active, sort, domain, None);

        // Rule vf(g(?x)) :- thing(?x), head g(?x) carried as a Value::Node.
        let xv = kb.fresh_var(vf);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let g_x = kb.alloc(Term::Fn {
            functor: g, pos_args: SmallVec::from_elem(xt, 1), named_args: SmallVec::new(),
        });
        let g_occ = node_occurrence::materialize_from_handle(&kb, g_x);
        let head = Value::Entity {
            functor: vf,
            pos: Rc::from(vec![Value::Node(g_occ)]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        let thing_x = kb.alloc(Term::Fn {
            functor: thing, pos_args: SmallVec::from_elem(xt, 1), named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[thing_x]);
        kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);

        let config = ResolveConfig::default();

        // Query vf(g(?y)) → 1 solution with ?y = "active".
        let yv = kb.fresh_var(vf);
        let yt = kb.alloc(Term::Var(Var::Global(yv)));
        let g_y = kb.alloc(Term::Fn {
            functor: g, pos_args: SmallVec::from_elem(yt, 1), named_args: SmallVec::new(),
        });
        let q_var = kb.alloc(Term::Fn {
            functor: vf, pos_args: SmallVec::from_elem(g_y, 1), named_args: SmallVec::new(),
        });
        let sols = kb.resolve(&[q_var], &config);
        assert_eq!(sols.len(), 1, "vf(g(?y)) should resolve through the value rule head");
        let bound = kb.reify(yt, &sols[0].subst).expect_term();
        assert_eq!(bound, active, "nested ?y must bind to \"active\", got {:?}", bound);

        // Query vf(g("active")) → succeeds (body thing("active") holds).
        let g_active = kb.alloc(Term::Fn {
            functor: g, pos_args: SmallVec::from_elem(active, 1), named_args: SmallVec::new(),
        });
        let q_ok = kb.alloc(Term::Fn {
            functor: vf, pos_args: SmallVec::from_elem(g_active, 1), named_args: SmallVec::new(),
        });
        assert_eq!(kb.resolve(&[q_ok], &config).len(), 1, "vf(g(\"active\")) should hold");

        // Query vf(g("missing")) → fails (no thing("missing")).
        let missing = kb.alloc(Term::Const(Literal::String("missing".into())));
        let g_missing = kb.alloc(Term::Fn {
            functor: g, pos_args: SmallVec::from_elem(missing, 1), named_args: SmallVec::new(),
        });
        let q_no = kb.alloc(Term::Fn {
            functor: vf, pos_args: SmallVec::from_elem(g_missing, 1), named_args: SmallVec::new(),
        });
        assert_eq!(kb.resolve(&[q_no], &config).len(), 0, "vf(g(\"missing\")) should fail");
    }

    #[test]
    fn with_fresh_vars_reifies_synthetic_non_term_binding() {
        // WI-636: a synthetic `u32::MAX - n` head-match entry bound to a NON-Term
        // Value (a scalar) must reach `body_rename` and substitute into the body.
        // The old `iter_terms` walk narrowed to `Value::Term` and SILENTLY dropped
        // it, leaving the body running on an unbound fresh var (the head-match
        // constraint lost). Build rule `p(?x) :- q(?x)`, hand-feed "DeBruijn 0
        // matched scalar 5" as a `Value::Int` synthetic entry, and assert the
        // opened body is `q(5)` — not `q(?fresh)`.
        use crate::eval::value::Value;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        let p = kb.intern("p");
        let q = kb.intern("q");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("d");

        // Rule p(?x) :- q(?x), arity 1 (closed to De Bruijn on assert).
        let xv = kb.fresh_var(p);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let head = kb.alloc(Term::Fn {
            functor: p, pos_args: SmallVec::from_elem(xt, 1), named_args: SmallVec::new(),
        });
        let body_q = kb.alloc(Term::Fn {
            functor: q, pos_args: SmallVec::from_elem(xt, 1), named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[body_q]);
        let rid = kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);
        assert_eq!(kb.rule_arity(rid), 1, "?x is the rule's one head var");

        // tree_subst: synthetic entry (DeBruijn 0 → scalar 5) as a NON-Term Value.
        let mut tree_subst = subst::Substitution::new();
        tree_subst.bind_value(&kb, Var::DeBruijn(0).as_vid(), Value::Int(5));

        let (fresh_nodes, _links) = kb.with_fresh_vars(rid, &tree_subst);
        assert_eq!(fresh_nodes.len(), 1, "one body atom q(?x)");

        // Body must be q(5): the scalar reached body_rename and substituted in.
        let body_term = node_occurrence::occurrence_to_term(&mut kb, &fresh_nodes[0]);
        let five = kb.alloc(Term::Const(Literal::Int(5)));
        let expected = kb.alloc(Term::Fn {
            functor: q, pos_args: SmallVec::from_elem(five, 1), named_args: SmallVec::new(),
        });
        assert_eq!(
            body_term, expected,
            "synthetic scalar head-match must substitute into the body (q(5)), \
             not be dropped as an unbound fresh var",
        );
    }

    #[test]
    fn with_fresh_vars_reifies_synthetic_entity_with_scalar_children() {
        // WI-636: an `Entity` operand with reifiable (scalar) children — the
        // common shape the WI-625 eq/neq bridge feeds into a rule-backed `eq`
        // head match — reifies faithfully and fires the rule, instead of being
        // dropped by the old `iter_terms` narrowing. Head `p(?x)`, body `q(?x)`,
        // synthetic entry (DeBruijn 0 → `mk(1, 2)` as a `Value::Entity`); assert
        // the opened body is `q(mk(1, 2))` and the candidate is NOT dropped.
        use crate::eval::value::Value;
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        let p = kb.intern("p");
        let q = kb.intern("q");
        let mk = kb.intern("mk");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("d");

        let xv = kb.fresh_var(p);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let head = kb.alloc(Term::Fn {
            functor: p, pos_args: SmallVec::from_elem(xt, 1), named_args: SmallVec::new(),
        });
        let body_q = kb.alloc(Term::Fn {
            functor: q, pos_args: SmallVec::from_elem(xt, 1), named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[body_q]);
        let rid = kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);

        let entity = Value::Entity {
            functor: mk,
            pos: Rc::from(vec![Value::Int(1), Value::Int(2)]),
            named: Rc::from(Vec::<(crate::intern::Symbol, Value)>::new()),
        };
        let mut tree_subst = subst::Substitution::new();
        tree_subst.bind_value(&kb, Var::DeBruijn(0).as_vid(), entity);

        let (fresh_nodes, links) = kb.with_fresh_vars(rid, &tree_subst);
        assert!(!links.is_contradiction(), "a reifiable Entity must NOT drop the candidate");
        assert_eq!(fresh_nodes.len(), 1);

        let body_term = node_occurrence::occurrence_to_term(&mut kb, &fresh_nodes[0]);
        let one = kb.alloc(Term::Const(Literal::Int(1)));
        let two = kb.alloc(Term::Const(Literal::Int(2)));
        let mk_12 = kb.alloc(Term::Fn {
            functor: mk, pos_args: SmallVec::from_slice(&[one, two]), named_args: SmallVec::new(),
        });
        let expected = kb.alloc(Term::Fn {
            functor: q, pos_args: SmallVec::from_elem(mk_12, 1), named_args: SmallVec::new(),
        });
        assert_eq!(body_term, expected, "Entity with scalar children must reify into the body");
    }

    #[test]
    fn with_fresh_vars_drops_candidate_on_unreifiable_carrier() {
        // WI-636: a carrier with no faithful term form reaching a head match must
        // NOT panic (that would abort the process on legitimate user input — the
        // WI-625 eq/neq bridge routes a `Value::Entity{ctor, [Value::Tuple…]}`
        // operand here) and must NOT be silently dropped into an unbound-var wrong
        // answer. Instead the candidate is dropped (`contradiction`), so eq falls
        // back to its structural verdict. Feed `mk(tuple(1, 2))` — an Entity
        // carrying a term-less `Value::Tuple`, the exact reachable shape — and
        // assert the returned links are a contradiction (candidate dropped).
        use crate::eval::value::Value;
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        let p = kb.intern("p");
        let q = kb.intern("q");
        let mk = kb.intern("mk");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("d");

        let xv = kb.fresh_var(p);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let head = kb.alloc(Term::Fn {
            functor: p, pos_args: SmallVec::from_elem(xt, 1), named_args: SmallVec::new(),
        });
        let body_q = kb.alloc(Term::Fn {
            functor: q, pos_args: SmallVec::from_elem(xt, 1), named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[body_q]);
        let rid = kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);

        // A term-less Tuple nested in an Entity — value_to_term recurses into the
        // Tuple child and errors, so the whole candidate is dropped.
        let tuple = Value::Tuple {
            pos: Rc::from(vec![Value::Int(1), Value::Int(2)]),
            named: Rc::from(Vec::<(crate::intern::Symbol, Value)>::new()),
        };
        let entity = Value::Entity {
            functor: mk,
            pos: Rc::from(vec![tuple]),
            named: Rc::from(Vec::<(crate::intern::Symbol, Value)>::new()),
        };
        let mut tree_subst = subst::Substitution::new();
        tree_subst.bind_value(&kb, Var::DeBruijn(0).as_vid(), entity);

        let (fresh_nodes, links) = kb.with_fresh_vars(rid, &tree_subst);
        assert!(
            links.is_contradiction(),
            "an un-reifiable carrier must drop the candidate (contradiction), not panic/leak",
        );
        assert!(fresh_nodes.is_empty(), "dropped candidate yields no body nodes");
    }

    #[test]
    fn prove_rule_predicate_no_panic_on_entity_tuple_operand() {
        // WI-636 end-to-end: this replicates the reachable path the WI-625 eq/neq
        // bridge drives — `prove_rule_predicate` builds an Entity goal from raw
        // ground operands and resolves it through `with_fresh_vars`. An operand
        // that is a `Value::Entity` carrying a term-less `Value::Tuple` used to
        // panic (aborting the process); it must now resolve without crashing, the
        // rule candidate dropping so the predicate is simply unproved (`Refuted`).
        use crate::eval::value::Value;
        use crate::kb::resolve::PredicateProof;
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        let pr = kb.intern("pr");
        let marker = kb.intern("marker");
        let mk = kb.intern("mk");
        let sort = ClauseKind::Fact;
        let domain = kb.intern("d");

        // Fact `marker` + rule `pr(?a, ?b) :- marker` (arity 2 → De Bruijn path).
        let marker_t = kb.alloc(Term::Fn {
            functor: marker, pos_args: SmallVec::new(), named_args: SmallVec::new(),
        });
        kb.assert_fact(marker_t, sort, domain, None);
        let av = kb.fresh_var(pr);
        let at = kb.alloc(Term::Var(Var::Global(av)));
        let bv = kb.fresh_var(pr);
        let bt = kb.alloc(Term::Var(Var::Global(bv)));
        let head = kb.alloc(Term::Fn {
            functor: pr, pos_args: SmallVec::from_slice(&[at, bt]), named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[marker_t]);
        kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);

        // Operand `mk(tuple(1, 2))`: an Entity carrying a term-less Tuple.
        let tuple = Value::Tuple {
            pos: Rc::from(vec![Value::Int(1), Value::Int(2)]),
            named: Rc::from(Vec::<(crate::intern::Symbol, Value)>::new()),
        };
        let entity = Value::Entity {
            functor: mk,
            pos: Rc::from(vec![tuple]),
            named: Rc::from(Vec::<(crate::intern::Symbol, Value)>::new()),
        };

        // No panic; the candidate drops, so the predicate is unproved.
        let proof = kb.prove_rule_predicate(pr, vec![entity, Value::Int(0)]);
        assert!(
            matches!(proof, PredicateProof::Refuted),
            "un-reifiable operand → dropped candidate → Refuted (no crash)",
        );
    }

    #[test]
    fn retract_removes_from_index() {
        let mut kb = KnowledgeBase::new();
        let sort = ClauseKind::Fact;
        let domain = kb.intern("d");
        let term = kb.alloc(Term::Const(Literal::Int(42)));

        let fid = kb.assert_fact(term, sort, domain, None);
        // WI-922: probes `by_domain`, not the retired `by_sort`. A `Const` head
        // has no functor, so `rules_by_functor` never held this fact — the domain
        // index is the one retract must be shown to maintain for it.
        assert_eq!(kb.by_domain(domain).len(), 1);

        kb.retract(fid);
        assert_eq!(kb.by_domain(domain).len(), 0);
    }

    #[test]
    fn match_term_const() {
        let mut kb = KnowledgeBase::new();
        let a = kb.alloc(Term::Const(Literal::Int(42)));
        let b = kb.alloc(Term::Const(Literal::Int(42)));
        let c = kb.alloc(Term::Const(Literal::Int(99)));

        assert!(kb.match_term(a, b).is_some());
        assert!(kb.match_term(a, c).is_none());
    }

    #[test]
    fn match_term_var_binds() {
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_term = kb.alloc(Term::Var(Var::Global(vid)));
        let target = kb.alloc(Term::Const(Literal::Int(42)));

        let s = kb.match_term(var_term, target).expect("should match");
        assert_eq!(s.resolve_as_value(vid).map(|v| v.expect_term()), Some(target));
    }

    #[test]
    fn match_term_var_consistency() {
        // ?x matches first arg, then must match same value in second arg
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_term = kb.alloc(Term::Var(Var::Global(vid)));

        let f_sym = kb.intern("f");
        let val = kb.alloc(Term::Const(Literal::Int(1)));

        // Pattern: f(?x, ?x)
        let pattern = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[var_term, var_term]),
            named_args: SmallVec::new(),
        });

        // Target: f(1, 1) — should match
        let target_ok = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[val, val]),
            named_args: SmallVec::new(),
        });
        assert!(kb.match_term(pattern, target_ok).is_some());

        // Target: f(1, 2) — should fail (inconsistent binding for ?x)
        let val2 = kb.alloc(Term::Const(Literal::Int(2)));
        let target_bad = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[val, val2]),
            named_args: SmallVec::new(),
        });
        assert!(kb.match_term(pattern, target_bad).is_none());
    }

    #[test]
    fn match_term_nonlinear_is_matching_not_unification() {
        // WI-633 boundary: a nonlinear pattern var `?x` in `f(?x, ?x)` MATCHES
        // only structurally-IDENTICAL target subterms. Against `f(some(?a),
        // some(?b))` with DISTINCT target vars, matching must FAIL — `match_term`
        // (and its `match_view` core, which drives the typer's simp_rewrite and
        // hypothesis discharge) is one-directional: it must NOT unify the two
        // target subterms by binding `?a := ?b`. The SLD resolution path unifies
        // instead (`resolve_leaf` `unify_rebind = true`); this locks that
        // `match_view` stays on `unify_rebind = false`. A regression here would
        // silently mis-fire nonlinear `[simp]` rules (Map.get / Set.member) on
        // distinct-key redexes, dropping the equality constraint.
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_term = kb.alloc(Term::Var(Var::Global(vid)));
        let f_sym = kb.intern("f");
        let some_sym = kb.intern("some");
        let pattern = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[var_term, var_term]),
            named_args: SmallVec::new(),
        });

        let mk_some = |kb: &mut KnowledgeBase, name: &str| {
            let a_sym = kb.intern(name);
            let av = kb.fresh_var(a_sym);
            let avt = kb.alloc(Term::Var(Var::Global(av)));
            kb.alloc(Term::Fn {
                functor: some_sym,
                pos_args: SmallVec::from_elem(avt, 1),
                named_args: SmallVec::new(),
            })
        };
        let some_a = mk_some(&mut kb, "a");
        let some_b = mk_some(&mut kb, "b");
        // Target: f(some(?a), some(?b)), ?a ≠ ?b — distinct but UNIFIABLE.
        let target_distinct = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[some_a, some_b]),
            named_args: SmallVec::new(),
        });
        assert!(
            kb.match_term(pattern, target_distinct).is_none(),
            "nonlinear pattern must MATCH (structural identity), not UNIFY distinct target vars"
        );

        // Same structure at both positions (some(?a), some(?a)) → matches.
        let target_same = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[some_a, some_a]),
            named_args: SmallVec::new(),
        });
        assert!(
            kb.match_term(pattern, target_same).is_some(),
            "identical target subterms at the repeated position must match"
        );
    }

    #[test]
    fn match_term_fn_structure() {
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("f");
        let g = kb.intern("g");
        let val = kb.alloc(Term::Const(Literal::Int(1)));

        let term_f = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        let term_g = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        // Same functor + args → matches
        assert!(kb.match_term(term_f, term_f).is_some());
        // Different functor → fails
        assert!(kb.match_term(term_f, term_g).is_none());
    }

    #[test]
    fn match_view_against_value_entity() {
        // Pattern `Account(?x)` (TermId) matched against a runtime
        // `Value::Entity { functor: Account, pos: [Value::Str("A001")] }`.
        // Proves the Q2 goal: rule-head patterns can unify with
        // non-TermId Value targets without promoting them into TermStore.
        use crate::eval::value::Value;

        let mut kb = KnowledgeBase::new();
        let f = kb.intern("Account");
        let x_sym = kb.intern("x");
        let xv = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(xv)));
        let pattern = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let value_target = Value::Entity {
            functor: f,
            pos: vec![Value::Str("A001".into())].into(),
            named: Vec::new().into(),
        };

        let subst = kb.match_view(pattern, &value_target)
            .expect("match should succeed");
        // ?x's binding is the Value (not a TermId) — lineage preserved.
        match subst.resolve_as_value(xv) {
            Some(Value::Str(s)) => assert_eq!(s, "A001"),
            other => panic!("expected Value::Str, got {other:?}"),
        }
        // resolve() returns None because the binding isn't a TermId.
        assert!(!matches!(subst.resolve_as_value(xv), Some(Value::Term { .. })));
    }

    #[test]
    fn match_view_binds_target_var_but_oneway_does_not() {
        // Regression guard (simp-rewriter convergence). `match_view` is the
        // WILDCARD matcher: a flex-`Global` var on the TARGET side binds to the
        // pattern's concrete subterm. This is load-bearing for assumed-fact
        // (WI-108 / Γ) discharge — `match_view(ground_fact, &goal)` must bind the
        // goal's query var, e.g. discharge subgoal `even(?y)` by hypothesis
        // `even(2)` binding `?y = 2`. `match_view_oneway` (the simp rewriter's
        // matcher) instead treats the target var as INERT and does NOT match.
        // Flipping `match_view` itself to one-way silently broke hypothesis
        // discharge (a var goal no longer discharged by a ground fact).
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("even");
        let two = kb.alloc(Term::Const(crate::kb::term::Literal::Int(2)));
        let pattern = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_elem(two, 1),
            named_args: SmallVec::new(),
        });
        let y_sym = kb.intern("y");
        let yv = kb.fresh_var(y_sym);
        let var_y = kb.alloc(Term::Var(Var::Global(yv)));
        let target = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_elem(var_y, 1),
            named_args: SmallVec::new(),
        });

        // Wildcard `match_view`: the target's `?y` binds to the pattern's `2`.
        let subst = kb
            .match_view(pattern, &term_view::TermIdView(target))
            .expect("wildcard match_view binds the target var");
        assert_eq!(
            kb.reify(var_y, &subst).expect_term(),
            two,
            "match_view must bind the target's ?y to the ground pattern's 2",
        );

        // One-directional `match_view_oneway`: the target var is inert → no match.
        assert!(
            kb.match_view_oneway(pattern, &term_view::TermIdView(target)).is_none(),
            "match_view_oneway must NOT bind a target var (the hypothesis-discharge break)",
        );
    }

    #[test]
    fn match_view_binds_vars_to_nested_value_entities() {
        // Pattern `Pair(?x, ?y)` matched against a runtime
        // `Pair(Entity{ inner(a: 1, b: "hi") }, Tuple(2, Entity{ leaf }))`.
        // Proves variables capture non-trivial structured Values out of
        // Substitution — the core WI-045/Q1 contract for external-source
        // bindings that must not be promoted to TermId.
        use crate::eval::value::Value;

        let mut kb = KnowledgeBase::new();
        let pair = kb.intern("Pair");
        let inner = kb.intern("Inner");
        let leaf = kb.intern("Leaf");
        let a_field = kb.intern("a");
        let b_field = kb.intern("b");

        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let xv = kb.fresh_var(x_sym);
        let yv = kb.fresh_var(y_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(xv)));
        let var_y = kb.alloc(Term::Var(Var::Global(yv)));
        let pattern = kb.alloc(Term::Fn {
            functor: pair,
            pos_args: SmallVec::from_slice(&[var_x, var_y]),
            named_args: SmallVec::new(),
        });

        let inner_val = Value::Entity {
            functor: inner,
            pos: Vec::new().into(),
            named: vec![(a_field, Value::Int(1)), (b_field, Value::Str("hi".into()))].into(),
        };
        let leaf_val = Value::Entity { functor: leaf, pos: Vec::new().into(), named: Vec::new().into() };
        let nested_tuple = Value::Tuple {
            pos: vec![Value::Int(2), leaf_val.clone()].into(),
            named: Vec::new().into(),
        };
        let target = Value::Entity {
            functor: pair,
            pos: vec![inner_val.clone(), nested_tuple.clone()].into(),
            named: Vec::new().into(),
        };

        let subst = kb.match_view(pattern, &target).expect("match should succeed");

        match subst.resolve_as_value(xv) {
            Some(Value::Entity { functor, named, .. }) => {
                assert_eq!(*functor, inner);
                assert_eq!(named.len(), 2);
                assert!(named.iter().any(|(k, v)|
                    *k == a_field && matches!(v, Value::Int(1))));
                assert!(named.iter().any(|(k, v)|
                    *k == b_field && matches!(v, Value::Str(s) if s == "hi")));
            }
            other => panic!("expected Value::Entity(Inner) for ?x, got {other:?}"),
        }

        match subst.resolve_as_value(yv) {
            Some(Value::Tuple { pos, .. }) => {
                assert_eq!(pos.len(), 2);
                assert!(matches!(pos[0], Value::Int(2)));
                match &pos[1] {
                    Value::Entity { functor, .. } => assert_eq!(*functor, leaf),
                    other => panic!("expected nested Leaf entity, got {other:?}"),
                }
            }
            other => panic!("expected Value::Tuple for ?y, got {other:?}"),
        }

        // Both variables bind to non-Term Values → resolve() returns None.
        assert!(!matches!(subst.resolve_as_value(xv), Some(Value::Term { .. })));
        assert!(!matches!(subst.resolve_as_value(yv), Some(Value::Term { .. })));
    }

    #[test]
    fn match_view_binds_vars_to_node_occurrence_children() {
        // WI-276: a `[simp]` rule LHS `add(?a, ?b)` (TermId pattern) matches a
        // reflect Expr occurrence `Value::Node(add(1, 2))` and binds ?a/?b to
        // the child occurrences (identity preserved, not promoted to TermId).
        // This is the substrate that lets the typer-phase rewriting engine
        // (proposal 043) fire simp rules over expression occurrences.
        use crate::eval::value::Value;
        use crate::kb::node_occurrence::{Expr, NodeOccurrence};
        use crate::kb::term::Literal;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;

        let mut kb = KnowledgeBase::new();
        let add = kb.intern("add");
        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let av = kb.fresh_var(a_sym);
        let bv = kb.fresh_var(b_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(av)));
        let var_b = kb.alloc(Term::Var(Var::Global(bv)));
        let pattern = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });

        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);
        let child_a = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let child_b = NodeOccurrence::new_expr(Expr::Const(Literal::Int(2)), span, None);
        let add_occ = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: add,
                pos_args: vec![Rc::clone(&child_a), Rc::clone(&child_b)],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );
        let target = Value::Node(add_occ);

        let subst = kb.match_view(pattern, &target).expect("match should succeed");

        match subst.resolve_as_value(av) {
            Some(Value::Node(occ)) => {
                assert!(matches!(occ.as_expr(), Some(Expr::Const(Literal::Int(1)))));
                assert!(Rc::ptr_eq(&occ, &child_a), "?a should bind the same Rc child");
            }
            other => panic!("expected Value::Node for ?a, got {other:?}"),
        }
        match subst.resolve_as_value(bv) {
            Some(Value::Node(occ)) => {
                assert!(matches!(occ.as_expr(), Some(Expr::Const(Literal::Int(2)))));
                assert!(Rc::ptr_eq(&occ, &child_b), "?b should bind the same Rc child");
            }
            other => panic!("expected Value::Node for ?b, got {other:?}"),
        }
        // Non-Term bindings → narrowing to a term returns None (lineage preserved).
        assert!(!matches!(subst.resolve_as_value(av), Some(Value::Term { .. })));
        assert!(!matches!(subst.resolve_as_value(bv), Some(Value::Term { .. })));
    }

    #[test]
    fn wi342_value_carried_modify_c_arrow_reads_through_termview() {
        // WI-342 P1+P2 slice. Build a real `(Cell) -> Unit ! {-Modify[c]}` arrow
        // as a Value-carried occurrence spine: the `denoted(c)` carries an
        // Rc<NodeOccurrence>, so the carrier rule poisons every container up to
        // `arrow` — each is `NodeKind::Type` / `NodeKind::EffectExpr`, while
        // ground children (param/result/sort_ref/empty_row) stay hash-consed
        // `TermId`. Assert it reads back through `TermView` with the SAME functor
        // surface as its `Term::Fn` twin, and that the `denoted` is reached
        // (Rep A: via the type-specific `as_type` walk for `bindings`) carrying
        // the identity-bearing occurrence the producer built.
        use crate::kb::load::register_prelude;
        use crate::kb::node_occurrence::{Expr, TypeChild, TypeNode};
        use crate::kb::term_view::{TermView, ViewHead, ViewItem};
        use crate::span::{SourceId, SourceSpan};

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let c_sym = kb.intern("c");
        let modify_sym = kb.intern("Modify");
        let t_sym = kb.intern("T");
        let param_ty = kb.make_sort_ref_by_name("Cell");
        let result_ty = kb.make_sort_ref_by_name("Unit");

        // `modify_base` and `empty_row_tid` are ground children the Value-carried
        // spine reuses below. WI-366: the former ground "TermId twin" of the whole
        // arrow (built via the retired `make_denoted`) is gone — production never
        // builds a ground `denoted`, so the cross-carrier identity comparison it
        // fed was dead-path; the Value-form reads below stand on their own.
        let modify_base = kb.make_sort_ref(modify_sym);
        let empty_row_tid = kb.make_effect_expression_empty_row();

        let arrow_sym = kb.resolve_symbol("anthill.prelude.TypeExtractor.Arrow");
        let effects_rows_sym = kb.resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows");
        let merge_sym = kb.resolve_symbol("anthill.prelude.EffectExpression.merge");
        let absent_sym = kb.resolve_symbol("anthill.prelude.EffectExpression.absent");

        let param_key = kb.intern("param");
        let result_key = kb.intern("result");
        let effects_key = kb.intern("effects");
        let effects_expr_key = kb.intern("effects_expr");
        let left_key = kb.intern("left");
        let right_key = kb.intern("right");
        let label_key = kb.intern("label");

        // ── Value-carried spine (the new producer builders). ──
        let denoted_occ = kb.make_denoted_occ_ref(c_sym, span, None);
        let param_occ = kb.make_parameterized_occ(
            TypeChild::Ground(modify_base),
            vec![(t_sym, TypeChild::Node(Rc::clone(&denoted_occ)))],
            span,
            None,
        );
        let absent_occ = kb.make_absent_occ(TypeChild::Node(Rc::clone(&param_occ)), span, None);
        let merge_occ = kb.make_merge_occ(
            TypeChild::Node(Rc::clone(&absent_occ)),
            TypeChild::Ground(empty_row_tid),
            span,
            None,
        );
        let effects_rows_occ =
            kb.make_effects_rows_occ(TypeChild::Node(Rc::clone(&merge_occ)), span, None);
        let arrow_occ = kb.make_arrow_occ(
            TypeChild::Ground(param_ty),
            TypeChild::Ground(result_ty),
            TypeChild::Node(Rc::clone(&effects_rows_occ)),
            1,
            span,
            None,
        );

        let functor_of = |h: &ViewHead| match h {
            ViewHead::Functor { functor, .. } => *functor,
            _ => None,
        };

        // Carrier identity: the Value-form arrow head is the `Arrow` functor.
        let head = arrow_occ.head(&kb);
        assert_eq!(functor_of(&head), Some(arrow_sym));
        assert!(
            matches!(head, ViewHead::Functor { named_arity: 4, pos_arity: 0, .. }),
            "arrow exposes param/result/effects + the WI-791 arity, got {head:?}",
        );

        // arrow.param / arrow.result are ground (no denoted) → hash-consed Terms.
        let p = arrow_occ.named_arg(&kb, param_key).expect("arrow.param");
        assert!(matches!(p, ViewItem::Term(t) if t == param_ty), "param ground, got {p:?}");
        let r = arrow_occ.named_arg(&kb, result_key).expect("arrow.result");
        assert!(matches!(r, ViewItem::Term(t) if t == result_ty), "result ground, got {r:?}");

        // Walk the poisoned spine through `TermView`, functor by functor.
        let eff = arrow_occ.named_arg(&kb, effects_key).expect("arrow.effects");
        assert_eq!(functor_of(&eff.head(&kb)), Some(effects_rows_sym));

        let merge_v = eff.named_arg(&kb, effects_expr_key).expect("effects_rows.effects_expr");
        assert_eq!(functor_of(&merge_v.head(&kb)), Some(merge_sym));

        // merge.left is poisoned (Node → absent); merge.right is the ground
        // `empty_row` (Term), proving ground subtrees stay hash-consed.
        let left = merge_v.named_arg(&kb, left_key).expect("merge.left");
        assert_eq!(functor_of(&left.head(&kb)), Some(absent_sym));
        let right = merge_v.named_arg(&kb, right_key).expect("merge.right");
        assert!(
            matches!(right, ViewItem::Term(t) if t == empty_row_tid),
            "merge.right is the ground empty_row Term, got {right:?}",
        );

        let paramd = left.named_arg(&kb, label_key).expect("absent.label");
        // WI-361: the parameterized carrier mirrors the term-backed `Fn{Modify, T}`
        // — its head functor IS the base sort `Modify` (no `parameterized` wrapper)
        // and the binding `T` reads as a named arg, so `TermView` reads the carrier
        // and its `Term::Fn` twin identically.
        assert_eq!(functor_of(&paramd.head(&kb)), Some(modify_sym));
        assert!(
            matches!(paramd.head(&kb), ViewHead::Functor { named_arity: 1, pos_arity: 0, .. }),
            "parameterized exposes its single binding T as a named arg, got {:?}",
            paramd.head(&kb),
        );

        // The binding value `T = denoted(c)` is reached as the named arg `T`,
        // carrying the identity-bearing occurrence (the poison source) — not a
        // hash-consed Term.
        let t_arg = paramd.named_arg(&kb, t_sym).expect("parameterized.T binding");
        let ViewItem::Node(denoted_seen) = &t_arg else {
            panic!("binding value is the poisoned denoted Node, got {t_arg:?}");
        };
        assert!(Rc::ptr_eq(denoted_seen, &denoted_occ), "denoted Rc identity preserved");

        // Storage is unchanged (`TypeNode::Parameterized { base, bindings }`); the
        // Rc identity of the carrier occurrence is preserved through the view.
        let ViewItem::Node(param_seen) = &paramd else {
            panic!("parameterized read as a Node occurrence, got {paramd:?}");
        };
        assert!(Rc::ptr_eq(param_seen, &param_occ), "view preserves Rc identity");
        let TypeNode::Denoted { value } =
            denoted_seen.as_type().expect("denoted is a Type node")
        else {
            panic!("expected Denoted");
        };
        assert!(
            matches!(value.as_expr(), Some(Expr::Ref(s)) if *s == c_sym),
            "denoted carries the source Ref(c) occurrence, got {:?}",
            value.as_expr(),
        );
        // The carried occurrence is NOT a hash-consed Ref — it is an
        // identity-bearing NodeOccurrence (the whole point of the carrier rule).
        assert!(
            value.as_type().is_none() && value.as_expr().is_some(),
            "denoted value is an Expr-kind occurrence",
        );
    }

    #[test]
    fn match_term_equals_match_view_of_termidview() {
        // For TermId-backed targets, match_term and match_view produce
        // structurally-equivalent substitutions. Proves the wrapper is
        // semantically transparent on the fast path.
        use crate::kb::term_view::TermIdView;

        let mut kb = KnowledgeBase::new();
        let f = kb.intern("pair");
        let x_sym = kb.intern("x");
        let xv = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(xv)));
        let lit = kb.alloc(Term::Const(Literal::Int(7)));
        let pattern = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_slice(&[var_x, lit]),
            named_args: SmallVec::new(),
        });
        let a = kb.alloc(Term::Const(Literal::Int(3)));
        let target = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_slice(&[a, lit]),
            named_args: SmallVec::new(),
        });

        let via_term = kb.match_term(pattern, target).expect("match_term");
        let via_view = kb.match_view(pattern, &TermIdView(target)).expect("match_view");

        assert_eq!(via_term.resolve_as_value(xv).map(|v| v.expect_term()), via_view.resolve_as_value(xv).map(|v| v.expect_term()));
        assert_eq!(via_term.resolve_as_value(xv).map(|v| v.expect_term()), Some(a));
    }

    #[test]
    fn subst_term_replaces_name() {
        let mut kb = KnowledgeBase::new();
        let t = kb.make_name_term("T");
        let int = kb.make_name_term("Int64");

        // Build Option(T) = Fn("Option", pos_args=[Fn("T",[])], named_args=[])
        let option_sym = kb.intern("Option");
        let option_t = kb.alloc(Term::Fn {
            functor: option_sym,
            pos_args: SmallVec::from_elem(t, 1),
            named_args: SmallVec::new(),
        });

        let result = kb.subst_term(option_t, t, int);
        match kb.get_term(result) {
            Term::Fn { functor, pos_args, .. } => {
                assert_eq!(*functor, option_sym);
                assert_eq!(pos_args.len(), 1);
                assert_eq!(pos_args[0], int);
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }

    #[test]
    fn subst_term_identity() {
        let mut kb = KnowledgeBase::new();
        let t = kb.make_name_term("T");
        let int = kb.make_name_term("Int64");
        let string = kb.make_name_term("String");

        // Substituting a name that doesn't appear should return the same term
        let result = kb.subst_term(t, int, string);
        assert_eq!(result, t);
    }

    #[test]
    fn subst_term_nested() {
        let mut kb = KnowledgeBase::new();
        let t = kb.make_name_term("T");
        let int = kb.make_name_term("Int64");

        // Build pair(T, T)
        let pair_sym = kb.intern("pair");
        let pair_tt = kb.alloc(Term::Fn {
            functor: pair_sym,
            pos_args: SmallVec::from_slice(&[t, t]),
            named_args: SmallVec::new(),
        });

        let result = kb.subst_term(pair_tt, t, int);
        match kb.get_term(result) {
            Term::Fn { pos_args, .. } => {
                // Both args should now be Int
                for &id in pos_args.iter() {
                    assert_eq!(id, int);
                }
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }

    #[test]
    fn query_by_pattern() {
        let mut kb = KnowledgeBase::new();
        let fact_sort = ClauseKind::Fact;
        let domain = kb.intern("test");
        let parent_sym = kb.intern("parent");

        // Assert parent("alice", "bob") and parent("bob", "charlie")
        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = kb.alloc(Term::Const(Literal::String("charlie".into())));

        let fact1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        let fact2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[bob, charlie]),
            named_args: SmallVec::new(),
        });

        kb.assert_fact(fact1, fact_sort, domain, None);
        kb.assert_fact(fact2, fact_sort, domain, None);

        // Query: parent(?x, "bob") — should find only fact1
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vid)));
        let pattern = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_x, bob]),
            named_args: SmallVec::new(),
        });

        let results = kb.query_view(&pattern);
        assert_eq!(results.len(), 1);
        let (_, ref s) = results[0];
        assert_eq!(s.resolve_as_value(vid).map(|v| v.expect_term()), Some(alice));
    }

    #[test]
    fn query_view_matches_via_value_node_goal() {
        // WI-246: a `Value::Node` occurrence goal finds the same candidate(s)
        // as the equivalent `TermId` goal — the matcher reads the goal only
        // through `TermView`, so an occurrence goal needs no lowering to a
        // hash-consed term to be looked up in the discrim tree.
        use crate::eval::value::Value;
        let mut kb = KnowledgeBase::new();
        let fact_sort = ClauseKind::Fact;
        let domain = kb.intern("test");
        let parent_sym = kb.intern("parent");
        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = kb.alloc(Term::Const(Literal::String("charlie".into())));
        let fact1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        let fact2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[bob, charlie]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact1, fact_sort, domain, None);
        kb.assert_fact(fact2, fact_sort, domain, None);

        // Goal `parent(?x, "bob")` built as a term, then materialized to an
        // occurrence and queried as a `Value::Node` — must match fact1 only,
        // binding ?x → "alice", identically to the `TermId` query.
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vid)));
        let pattern = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_x, bob]),
            named_args: SmallVec::new(),
        });
        let term_hits = kb.query_view(&pattern);

        let occ = node_occurrence::materialize_from_handle(&kb, pattern);
        let node_hits = kb.query_view(&Value::Node(occ));

        assert_eq!(node_hits.len(), 1, "Value::Node goal matches one fact");
        assert_eq!(node_hits.len(), term_hits.len(), "same candidate count as TermId goal");
        assert_eq!(node_hits[0].0, term_hits[0].0, "same matched rule/fact");
        assert_eq!(
            node_hits[0].1.resolve_as_value(vid).map(|v| v.expect_term()),
            Some(alice),
            "?x bound to \"alice\" via the occurrence goal",
        );
    }

    #[test]
    fn assert_rule_with_body() {
        let mut kb = KnowledgeBase::new();
        let rule_sort = ClauseKind::Rule;
        let domain = kb.intern("test");
        let parent_sym = kb.intern("parent");
        let grandparent_sym = kb.intern("grandparent");

        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let z_sym = kb.intern("z");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let vz = kb.fresh_var(z_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let var_z = kb.alloc(Term::Var(Var::Global(vz)));

        // grandparent(?x, ?z) :- parent(?x, ?y), parent(?y, ?z)
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

        let rid = kb.assert_rule(head, vec![b1, b2], rule_sort, domain, None);

        // body should have two atoms
        assert_eq!(kb.rule_body_nodes(rid).len(), 2);
        assert_eq!(kb.rule_head(rid), head);

        // fact_count should be 0, rule_count should be 1
        assert_eq!(kb.fact_count(), 0);
        assert_eq!(kb.rule_count(), 1);
    }

    #[test]
    fn query_rules_filters_facts() {
        let mut kb = KnowledgeBase::new();
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");
        let f_sym = kb.intern("f");

        // Assert a ground fact f(1)
        let v1 = kb.alloc(Term::Const(Literal::Int(1)));
        let fact_term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(v1, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact_term, sort, domain, None);

        // Assert a rule f(?x) :- g(?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let rule_head = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let g_sym = kb.intern("g");
        let body_lit = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(rule_head, vec![body_lit], sort, domain, None);

        // candidate selection should find both
        let q_sym = kb.intern("q");
        let qv = kb.fresh_var(q_sym);
        let var_q = kb.alloc(Term::Var(Var::Global(qv)));
        let pattern = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_q, 1),
            named_args: SmallVec::new(),
        });
        let candidates = kb.query_view(&pattern);
        assert_eq!(candidates.len(), 2);

        // The resolver sees one fact and one bodied rule.
        assert_eq!(
            candidates
                .iter()
                .filter(|(rid, _)| !kb.is_fact(*rid))
                .count(),
            1,
        );
    }

    #[test]
    fn apply_subst_replaces_vars() {
        let mut kb = KnowledgeBase::new();
        let f_sym = kb.intern("f");
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vid)));
        let val = kb.alloc(Term::Const(Literal::Int(42)));

        let term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let mut s = subst::Substitution::new();
        s.bind(&kb, vid, val);
        let result = kb.apply_subst(term, &s);

        match kb.get_term(result) {
            Term::Fn { pos_args, .. } => {
                assert_eq!(pos_args[0], val);
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }

    #[test]
    fn collect_vars_finds_all() {
        let mut kb = KnowledgeBase::new();
        let f_sym = kb.intern("f");
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));

        let term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[var_x, var_y, var_x]),
            named_args: SmallVec::new(),
        });

        let vars = kb.collect_vars(term);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&vx));
        assert!(vars.contains(&vy));
    }

    #[test]
    fn retract_releases_body_terms() {
        let mut kb = KnowledgeBase::new();
        let sort = ClauseKind::Rule;
        let domain = kb.intern("test");
        let f_sym = kb.intern("f");
        let g_sym = kb.intern("g");

        let val = kb.alloc(Term::Const(Literal::Int(99)));
        let head = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        let body_lit = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let rid = kb.assert_rule(head, vec![body_lit], sort, domain, None);
        assert_eq!(kb.rule_count(), 1);

        kb.retract(rid);
        assert_eq!(kb.rule_count(), 0);
        assert_eq!(kb.fact_count(), 0);
    }
}

/// WI-518: a guard riding an occurrence (`Value::Node`) leaf now RESOLVES through
/// `resolve_goals`, carrier-neutrally, exactly as a term leaf does — the WI-514
/// gate (which used to report such a guard `Gated` / refuse the assertion / panic)
/// has dissolved. These tests are the spike turned into regressions: an occurrence
/// self-loop constraint `no edge(?p, ?p)` lowered through the new `Vec<Value>` path
/// matches real self-loop facts, excludes non-self-loops, and enforces at both the
/// post-load `check_all_guards` pass and the per-assert runtime path.
#[cfg(test)]
mod wi518_occurrence_guard_resolution_tests {
    use super::*;
    use crate::eval::value::Value;
    use crate::intern::Symbol;
    use crate::kb::node_occurrence::{Expr, NodeOccurrence};
    use crate::span::{SourceId, SourceSpan};
    use smallvec::SmallVec;
    use std::rc::Rc;

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 0)
    }

    /// Register a `LogicalQuery` constructor symbol under its qualified name
    /// (`anthill.reflect.LogicalQuery.<short>`) and return it — mirroring the
    /// loader's `logical_query_ctor`. WI-513: the guard engine dispatches by the
    /// interned qualified `LogicalQuerySymbols`, so a guard built in a bare KB must
    /// use the SAME qualified symbol `LogicalQuerySymbols::resolve` will look up
    /// (an `intern("no_q")` short name would not match). Field-key symbols
    /// (`condition`/`body`/`term`/…) stay short-name interned — both sides intern
    /// them identically.
    fn lq_ctor(kb: &mut KnowledgeBase, short: &str) -> Symbol {
        let qn = format!("anthill.reflect.LogicalQuery.{short}");
        let root_scope = kb.global_scope();
        kb.symbols.define(short, &qn, SymbolKind::Operation, root_scope)
    }

    /// Build `no_q(condition: pattern_query(term: <leaf>), body: empty_query)` — a
    /// quantified guard around `leaf` (the top level is a quantifier so
    /// `evaluate_guard` descends into the shared lowerer). The leaf is any goal
    /// `Value`: a `Value::Term` for the hash-consed case, a `Value::Node` for an
    /// occurrence goal.
    fn no_q_guard(kb: &mut KnowledgeBase, leaf: Value) -> Value {
        let no_q = lq_ctor(kb, "no_q");
        let condition = kb.intern("condition");
        let body = kb.intern("body");
        let pattern_query = lq_ctor(kb, "pattern_query");
        let term = kb.intern("term");
        let empty_query = lq_ctor(kb, "empty_query");

        let pq = Value::Entity {
            functor: pattern_query,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(term, leaf)]),
        };
        let empty = Value::Entity {
            functor: empty_query,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        Value::Entity {
            functor: no_q,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(condition, pq), (body, empty)]),
        }
    }

    /// The occurrence goal `edge(?p, ?p)` — a self-loop pattern carrying a SHARED
    /// `Value::Node` variable across both positional slots, as a `denoted`
    /// occurrence would. This is the leaf the WI-514 gate used to refuse; WI-518
    /// resolves it.
    fn edge_self_loop_occurrence(kb: &mut KnowledgeBase) -> Value {
        let edge = kb.intern("edge");
        let p = kb.intern("p");
        let vid = kb.fresh_var(p);
        let var_occ = NodeOccurrence::new_expr(Expr::Var(Var::Global(vid)), span(), None);
        let ctor = NodeOccurrence::new_expr(
            Expr::Constructor {
                name: edge,
                pos_args: vec![var_occ.clone(), var_occ],
                named_args: Vec::new(),
                from_projection: false,
            },
            span(),
            None,
        );
        Value::Node(ctor)
    }

    /// Assert a ground `edge(from, to)` fact (both args nullary atoms).
    fn assert_edge(kb: &mut KnowledgeBase, domain: Symbol, from: &str, to: &str) -> RuleId {
        let edge = kb.intern("edge");
        let from_t = kb.make_name_term(from);
        let to_t = kb.make_name_term(to);
        let fact = kb.alloc(Term::Fn {
            functor: edge,
            pos_args: SmallVec::from_slice(&[from_t, to_t]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact, ClauseKind::Fact, domain, None)
    }

    /// The spike: a `no edge(?p, ?p)` guard whose condition is an OCCURRENCE leaf
    /// resolves through `resolve_goals` and is VIOLATED by a real self-loop fact
    /// (`edge(n1, n1)`) — never reported `Gated`. The shared `?p` is what makes
    /// the match a genuine self-loop check, not a blanket `edge` match.
    #[test]
    fn occurrence_self_loop_guard_violated_by_self_loop() {
        let mut kb = KnowledgeBase::new();
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");
        assert_edge(&mut kb, domain, "n1", "n1"); // a self-loop
        assert_edge(&mut kb, domain, "n2", "n3"); // not a self-loop

        let leaf = edge_self_loop_occurrence(&mut kb);
        let query = no_q_guard(&mut kb, leaf);
        kb.add_guard_labeled(query, Some("no_self_loop".to_string()));

        assert_eq!(
            kb.check_all_guards(),
            vec![GuardCheck::Violated(Some("no_self_loop".to_string()))],
            "an occurrence self-loop leaf must RESOLVE and be violated by edge(n1, n1)",
        );
    }

    /// The exclusion half: with only a NON-self-loop fact (`edge(n2, n3)`), the same
    /// occurrence guard `no edge(?p, ?p)` resolves to zero matches and HOLDS — the
    /// shared `?p` correctly excludes `edge(n2, n3)`.
    #[test]
    fn occurrence_self_loop_guard_holds_without_self_loop() {
        let mut kb = KnowledgeBase::new();
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");
        assert_edge(&mut kb, domain, "n2", "n3"); // not a self-loop

        let leaf = edge_self_loop_occurrence(&mut kb);
        let query = no_q_guard(&mut kb, leaf);
        kb.add_guard_labeled(query, Some("no_self_loop".to_string()));

        assert_eq!(
            kb.check_all_guards(),
            vec![GuardCheck::Holds],
            "an occurrence self-loop leaf must exclude edge(n2, n3) and hold",
        );
    }

    /// The per-assert runtime path (the one that USED to panic on an occurrence
    /// guard): with the `no edge(?p, ?p)` guard wired to the `Graph` sort,
    /// `assert_checked` of a self-loop fact resolves the occurrence guard, finds the
    /// just-inserted self-loop, and REJECTS the fact (returns `None`) — enforcing
    /// the invariant rather than panicking.
    #[test]
    fn occurrence_guard_enforced_at_assert_checked() {
        let mut kb = KnowledgeBase::new();
        // WI-922: the guard TRIGGER SORT and the clause KIND are separate
        // arguments now; this test used one value for both.
        let trigger_sort = kb.intern("Graph");
        let domain = kb.intern("test");

        let leaf = edge_self_loop_occurrence(&mut kb);
        let query = no_q_guard(&mut kb, leaf);
        let cid = kb.add_guard_labeled(query, Some("no_self_loop".to_string()));
        // The synthetic occurrence query carries no resolvable trigger sort, so wire
        // the guard to the asserted fact's sort by hand (the per-assert lookup keys
        // on `guards_by_sort`).
        kb.guards_by_sort.entry(trigger_sort).or_default().push(cid.index());

        let edge = kb.intern("edge");
        let n1 = kb.make_name_term("n1");
        let self_loop = kb.alloc(Term::Fn {
            functor: edge,
            pos_args: SmallVec::from_slice(&[n1, n1]),
            named_args: SmallVec::new(),
        });
        let rid = kb.assert_checked(self_loop, ClauseKind::Fact, trigger_sort, domain, None);
        assert!(
            rid.is_none(),
            "asserting a self-loop under `no edge(?p, ?p)` must be rejected (None), not panic",
        );
    }

    /// A term-leaf guard is unaffected: `no_q` with no matching facts holds.
    /// Guards against the carrier-neutral port regressing ordinary term constraints.
    #[test]
    fn term_leaf_guard_still_evaluates() {
        let mut kb = KnowledgeBase::new();
        // A hash-consed TermId leaf (a nullary `widget` atom) — never matched by
        // any fact, so `no_q` holds.
        let widget = kb.intern("widget");
        let leaf_term = kb.alloc(Term::Fn {
            functor: widget,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let query = no_q_guard(&mut kb, Value::term(leaf_term));
        kb.add_guard_labeled(query, Some("term_constraint".to_string()));

        assert_eq!(
            kb.check_all_guards(),
            vec![GuardCheck::Holds],
            "a term-leaf `no_q` with no matching facts must hold",
        );
    }

    /// `lower_logical_query`'s RECURSIVE `conjunction` arm threads goal `Value`s
    /// carrier-neutrally: a term leaf on the left, an occurrence leaf on the right.
    /// Both must lower and resolve — with a matching `flag()` fact and a self-loop
    /// `edge(n1, n1)`, the conjunction succeeds and the `no_q` is violated. (The
    /// WI-514 gate used to refuse the whole conjunction for the occurrence leaf.)
    #[test]
    fn conjunction_with_occurrence_leaf_resolves() {
        let mut kb = KnowledgeBase::new();
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");
        assert_edge(&mut kb, domain, "n1", "n1");
        // A nullary `flag()` fact for the term-leaf side.
        let flag = kb.intern("flag");
        let flag_fact = kb.alloc(Term::Fn {
            functor: flag,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(flag_fact, sort, domain, None);

        let no_q = lq_ctor(&mut kb, "no_q");
        let condition = kb.intern("condition");
        let body = kb.intern("body");
        let conjunction = lq_ctor(&mut kb, "conjunction");
        let left = kb.intern("left");
        let right = kb.intern("right");
        let pattern_query = lq_ctor(&mut kb, "pattern_query");
        let term = kb.intern("term");
        let empty_query = lq_ctor(&mut kb, "empty_query");

        // Left: a hash-consed `flag()` term leaf.
        let flag_leaf = kb.alloc(Term::Fn {
            functor: flag,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let pq_term = Value::Entity {
            functor: pattern_query,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(term, Value::term(flag_leaf))]),
        };
        // Right: the occurrence self-loop leaf.
        let pq_occ = Value::Entity {
            functor: pattern_query,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(term, edge_self_loop_occurrence(&mut kb))]),
        };
        let conj = Value::Entity {
            functor: conjunction,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(left, pq_term), (right, pq_occ)]),
        };
        let empty = Value::Entity {
            functor: empty_query,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        let query = Value::Entity {
            functor: no_q,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(condition, conj), (body, empty)]),
        };
        kb.add_guard_labeled(query, Some("conj_constraint".to_string()));

        assert_eq!(
            kb.check_all_guards(),
            vec![GuardCheck::Violated(Some("conj_constraint".to_string()))],
            "a conjunction mixing a term leaf and an occurrence leaf must resolve and be violated",
        );
    }
}

/// WI-628 (deferred half): the EAGER constraint / quantifier guards must not read
/// an `is_empty()` / short count from a DEPTH-TRUNCATED search as a verdict. A
/// `loop(?x) :- loop(?x)` recursion never terminates, so any guard resolving
/// `loop(a)` TRUNCATES at the default depth budget — the empty result is UNDECIDED,
/// and `check_all_guards` must report `GuardCheck::Undecidable` (which the loader
/// routes to a load-BLOCKING `ConstraintUndecidable`), NOT a silent `Holds`.
/// Contrast fixtures over a COMPLETE empty search confirm the flag does not
/// over-trigger. The `forall` `not(body)` truncation path (piece a) is covered at
/// the resolve layer by
/// `wi628_naf_truncation_propagates_to_outer_stream_under_definite_only`.
#[cfg(test)]
mod wi628_guard_truncation_tests {
    use super::*;
    use crate::eval::value::Value;
    use crate::intern::Symbol;
    use smallvec::SmallVec;
    use std::rc::Rc;

    /// Register a `LogicalQuery` ctor under its qualified name (mirrors the loader
    /// / the wi518 `lq_ctor`, so `LogicalQuerySymbols::resolve` finds it).
    fn lq_ctor(kb: &mut KnowledgeBase, short: &str) -> Symbol {
        let qn = format!("anthill.reflect.LogicalQuery.{short}");
        let root_scope = kb.global_scope();
        kb.symbols.define(short, &qn, SymbolKind::Operation, root_scope)
    }

    /// Assert `loop(?x) :- loop(?x)` — a non-terminating recursion that TRUNCATES at
    /// the depth budget for any ground `loop(_)` query (it never refutes).
    fn assert_loop_rule(kb: &mut KnowledgeBase, domain: Symbol) {
        let loop_sym = kb.intern("loop");
        let x = kb.intern("x");
        let vx = kb.fresh_var(x);
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
        kb.assert_rule(head, vec![body], ClauseKind::Rule, domain, None);
    }

    /// A `Value::Term` leaf `functor(atom)` where `atom` is a nullary name term.
    fn unary_leaf(kb: &mut KnowledgeBase, functor: &str, atom: &str) -> Value {
        let f = kb.intern(functor);
        let a = kb.make_name_term(atom);
        let t = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        Value::term(t)
    }

    fn pattern_query(kb: &mut KnowledgeBase, leaf: Value) -> Value {
        let pq = lq_ctor(kb, "pattern_query");
        let term = kb.intern("term");
        Value::Entity {
            functor: pq,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(term, leaf)]),
        }
    }

    fn entity(kb: &mut KnowledgeBase, short: &str, named: Vec<(Symbol, Value)>) -> Value {
        let f = lq_ctor(kb, short);
        Value::Entity {
            functor: f,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(named),
        }
    }

    /// `negation(query: pattern_query(term: leaf))`.
    fn negation_guard(kb: &mut KnowledgeBase, leaf: Value) -> Value {
        let query = kb.intern("query");
        let pq = pattern_query(kb, leaf);
        entity(kb, "negation", vec![(query, pq)])
    }

    /// `no_q(condition: pattern_query(term: leaf), body: empty_query)`.
    fn no_q_guard(kb: &mut KnowledgeBase, leaf: Value) -> Value {
        let condition = kb.intern("condition");
        let body = kb.intern("body");
        let pq = pattern_query(kb, leaf);
        let empty = entity(kb, "empty_query", Vec::new());
        entity(kb, "no_q", vec![(condition, pq), (body, empty)])
    }

    /// `forall_q(condition: pattern_query(term: leaf))` — no body, so no synthesized
    /// `not(...)`; the CONDITION goals drive the (truncating) search.
    fn forall_condition_guard(kb: &mut KnowledgeBase, leaf: Value) -> Value {
        let condition = kb.intern("condition");
        let pq = pattern_query(kb, leaf);
        entity(kb, "forall_q", vec![(condition, pq)])
    }

    /// Assert `check_all_guards` yielded exactly one `Undecidable(label, reason)`.
    fn expect_undecidable(checks: &[GuardCheck], label: &str) {
        match checks {
            [GuardCheck::Undecidable(Some(l), detail)] => {
                assert_eq!(l.as_str(), label, "undecidable finding carries the source label");
                assert!(
                    detail.contains("undecidable"),
                    "reason should name the undecidability: {detail}"
                );
            }
            other => panic!("expected [Undecidable(Some({label:?}), _)], got {other:?}"),
        }
    }

    fn loop_kb() -> (KnowledgeBase, Symbol) {
        let mut kb = KnowledgeBase::new();
        let domain = kb.intern("test");
        assert_loop_rule(&mut kb, domain);
        (kb, domain)
    }

    #[test]
    fn negation_guard_over_truncated_search_is_undecidable() {
        let (mut kb, _domain) = loop_kb();
        let leaf = unary_leaf(&mut kb, "loop", "a");
        let guard = negation_guard(&mut kb, leaf);
        kb.add_guard_labeled(guard, Some("no_loop".to_string()));
        expect_undecidable(&kb.check_all_guards(), "no_loop");
    }

    #[test]
    fn negation_guard_over_complete_empty_search_holds() {
        // Contrast: `g(a)` is undefined, so its search COMPLETES empty — the
        // negation holds DEFINITELY and must NOT be flagged undecidable, even
        // though the KB also contains the truncating `loop` rule (no over-trigger).
        let (mut kb, _domain) = loop_kb();
        let leaf = unary_leaf(&mut kb, "g", "a");
        let guard = negation_guard(&mut kb, leaf);
        kb.add_guard_labeled(guard, Some("no_g".to_string()));
        assert_eq!(kb.check_all_guards(), vec![GuardCheck::Holds]);
    }

    #[test]
    fn no_q_count_guard_over_truncated_search_is_undecidable() {
        // `no_q` (min=0, max=0) that found nothing might have missed a witness in a
        // branch cut at the depth limit — undecidable, not a silent hold.
        let (mut kb, _domain) = loop_kb();
        let leaf = unary_leaf(&mut kb, "loop", "a");
        let guard = no_q_guard(&mut kb, leaf);
        kb.add_guard_labeled(guard, Some("no_loop_count".to_string()));
        expect_undecidable(&kb.check_all_guards(), "no_loop_count");
    }

    #[test]
    fn forall_guard_over_truncated_condition_is_undecidable() {
        let (mut kb, _domain) = loop_kb();
        let leaf = unary_leaf(&mut kb, "loop", "a");
        let guard = forall_condition_guard(&mut kb, leaf);
        kb.add_guard_labeled(guard, Some("forall_loop".to_string()));
        expect_undecidable(&kb.check_all_guards(), "forall_loop");
    }
}

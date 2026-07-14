/// IR → KB loading.
///
/// Converts a parsed `ParsedFile` into KnowledgeBase terms and facts.
/// Re-interns symbols, re-allocates terms into the hash-consed store,
/// registers sorts, and asserts facts.
///
/// **Pipeline:** scan_definitions (define all names) → load (fill KB with facts).
///
/// The loader takes a `SourceResolver` to fetch imported files. The CLI
/// provides a real FS implementation; tests use `NullResolver`.

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::{Symbol, SymbolDef, SymbolKind, ScopeInclusion, ResolveResult};
use crate::parse::ir::*;
use crate::parse::pratt;
use crate::span::{Span, SourceId, SourceSpan};
use super::{KnowledgeBase, SortKind};
use super::term::{Term, TermId, Var, VarId, Literal};
use super::node_occurrence::{self, Expr, NodeOccurrence};
use super::resolve::{BuiltinTag, PositionalPlan};
use super::term_view::{TermIdView, TermView};
use super::typing::{binding_op_symbol, extract_sort_ref_sym, extract_type, TypeExtractor};
use crate::eval::value::Value;

// ── Load result ──────────────────────────────────────────────

/// Result of loading a file or set of files.
/// Contains the sort/enum terms defined, for targeted type checking.
#[derive(Debug, Default)]
pub struct LoadResult {
    /// Sort and enum terms defined during this load.
    pub defined_sorts: Vec<TermId>,
    /// RuleIds of facts asserted during this load, in source order.
    /// Parallel with `parsed.fact_spans()` so persistence backends can
    /// pair each fact's RuleId with its source byte range.
    pub fact_rule_ids: Vec<crate::kb::RuleId>,
    /// Non-fatal diagnostics accumulated during load (WI-345). Empty unless
    /// a pass emitted an advisory warning (e.g. WI-346 requires-shadow).
    /// Populated only on the `Ok` path: a failing load returns
    /// `Err(errors)` and drops warnings — you fix the errors first.
    pub warnings: Vec<LoadWarning>,
}

// ── Source resolution ──────────────────────────────────────────

/// Abstraction over the filesystem for resolving import paths to source text.
pub trait SourceResolver {
    /// Resolve a source path (e.g. `"std/prelude"` or `"./banking"`) to its contents.
    fn resolve(&self, path: &str) -> Result<String, std::io::Error>;
}

/// Resolves import paths by searching filesystem base directories.
///
/// Converts dotted import paths (e.g. `"anthill.prelude.List"`) to filesystem
/// paths (`"anthill/prelude/List.anthill"`) and searches each base directory.
pub struct FileSourceResolver {
    base_dirs: Vec<PathBuf>,
}

impl FileSourceResolver {
    pub fn new(base_dirs: Vec<PathBuf>) -> Self {
        Self { base_dirs }
    }
}

impl SourceResolver for FileSourceResolver {
    fn resolve(&self, path: &str) -> Result<String, std::io::Error> {
        let rel_path = path.replace('.', "/") + ".anthill";
        for base in &self.base_dirs {
            let full = base.join(&rel_path);
            if full.exists() {
                return std::fs::read_to_string(&full);
            }
        }
        Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("cannot resolve '{path}' in base dirs: {:?}", self.base_dirs),
        ))
    }
}

/// A resolver that always fails — for tests that don't use imports.
pub struct NullResolver;

impl SourceResolver for NullResolver {
    fn resolve(&self, path: &str) -> Result<String, std::io::Error> {
        Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("NullResolver: cannot resolve '{path}'"),
        ))
    }
}

/// Extract the last dot-separated segment from a qualified name.
fn last_segment(qualified: &str) -> &str {
    qualified.rsplit('.').next().unwrap_or(qualified)
}

/// Construct a fully-qualified name by prepending a prefix.
/// If prefix is empty, returns name as-is.
fn make_qualified(prefix: &str, name: &str) -> String {
    if prefix.is_empty() { name.to_owned() } else { format!("{}.{}", prefix, name) }
}

/// Join name segments into a single dot-separated string.
fn join_segments(symbols: &crate::intern::SymbolTable, segments: &[Symbol]) -> String {
    let mut out = String::new();
    for (i, &sym) in segments.iter().enumerate() {
        if i > 0 {
            out.push('.');
        }
        out.push_str(symbols.name(sym));
    }
    out
}

/// WI-510: the always-on disambiguating tag appended after `entity.field` in a
/// rendered `TypeMismatch` — ` (op-arg)` / ` (entity-field)` / … — so two checks
/// that flatten to the same names render distinguishably. Empty for loader-built
/// mismatches with no typer origin.
fn type_mismatch_tag(origin: &Option<TypeMismatchOrigin>) -> String {
    match origin {
        Some(o) => format!(" ({})", o.context_kind),
        None => String::new(),
    }
}

/// WI-510: the opt-in construction-site trace appended to a rendered
/// `TypeMismatch`, e.g. ` [Other @ kb/typing.rs:14028]`. Gated on the
/// `ANTHILL_DIAG_ORIGIN` env var so normal diagnostics stay clean; a developer
/// tracing a mismatch to its origin sets the var and re-runs. Empty otherwise.
fn type_mismatch_origin_suffix(origin: &Option<TypeMismatchOrigin>) -> String {
    match origin {
        Some(o) if std::env::var_os("ANTHILL_DIAG_ORIGIN").is_some() => {
            format!(" [{} @ {}:{}]", o.error_kind, o.site.file(), o.site.line())
        }
        _ => String::new(),
    }
}

/// WI-510: provenance of a `LoadError::TypeMismatch` that came from the typer's
/// `TypeError::to_load_error`. The typer flattens a structured `TypeErrorContext`
/// (`EntityField` / `OperationArgument` / …) plus `Value`-typed expected/actual
/// into plain display strings, so two structurally different checks can render
/// identically (WI-509 debugging cost). This marker preserves enough to (a) tag
/// the rendered message with the originating context variant — so `EntityField`
/// and `OperationArgument` mismatches are distinguishable — and (b) trace the
/// mismatch to its exact `TypeError::…{ … }` construction site (opt-in via the
/// `ANTHILL_DIAG_ORIGIN` env var, kept off normal output). `None` for
/// `TypeMismatch`es built directly by the loader (not via the typer).
#[derive(Clone, Copy, Debug)]
pub struct TypeMismatchOrigin {
    /// The `TypeError` variant name — `"TypeMismatch"` or `"Other"`.
    pub error_kind: &'static str,
    /// The `TypeErrorContext` variant tag — `"entity-field"`, `"op-arg"`, …
    pub context_kind: &'static str,
    /// The `TypeError::…{ … }` construction site (file:line:col).
    pub site: &'static std::panic::Location<'static>,
}

#[derive(Clone, Debug)]
pub enum LoadError {
    UnresolvedName {
        name: String,
        span: Span,
        scope_name: String,
    },
    UnresolvedImport {
        path: String,
        span: Span,
    },
    AmbiguousSymbol {
        name: String,
        candidates: Vec<String>,
        span: Span,
        scope_name: String,
    },
    TypeMismatch {
        entity_name: String,
        field_name: String,
        expected_type: String,
        actual_type: String,
        span: Option<Span>,
        /// WI-510: typer provenance — the originating `TypeError` context variant
        /// and construction site. `Some` when built by `TypeError::to_load_error`
        /// (for the lossy `TypeMismatch`/`Other` variants), `None` when the loader
        /// constructs a `TypeMismatch` directly.
        origin: Option<TypeMismatchOrigin>,
    },
    /// WI-343: a carrier provides a spec whose own `requires` is not
    /// satisfied by that carrier — e.g. `fact PersistentCollection[List]`
    /// where `PersistentCollection requires Iterable` but `List` provides
    /// no `Iterable`. The satisfaction fact is unsound: the spec's contract
    /// does not hold for the carrier.
    UnsatisfiedProviderRequires {
        carrier: String,
        spec: String,
        required: String,
    },
    /// WI-363: a carrier provides a spec but does not back one of the spec's
    /// declared operations. The op-level twin of `UnsatisfiedProviderRequires`:
    /// `fact Spec[X]` is trusted by the typer, yet `Spec.op` has neither a
    /// spec-level default (an `operation … = …` body or a derivation rule on
    /// `Spec`) nor an operation `X` itself supplies — so a call resolves to
    /// nothing at runtime. Load-blocking: the satisfaction fact is unsound.
    UnbackedProviderOperation {
        carrier: String,
        spec: String,
        op: String,
    },
    /// WI-658: a carrier provides BOTH `Eq` (lawful, reflexive equality) and
    /// `NonEq` (a WITNESSED non-reflexive equality — `nonEqRefl()` exhibits a
    /// value unequal to itself). They are mutually exclusive: a carrier's `eq`
    /// cannot be both reflexive and non-reflexive. A partial carrier (IEEE
    /// `Float`) provides `PartialEq` + `NonEq`; a lawful carrier provides
    /// `PartialEq` + `Eq`. Load-blocking: the two provisions contradict. Note
    /// the check is opt-in — a carrier that provides neither is unconstrained.
    IncompatibleEqNonEq {
        carrier: String,
    },
    /// WI-644: a parametric sort with a `requires Eq[param]` clause is
    /// instantiated (in an entity field type) with `param` bound to a carrier
    /// that provides `NonEq` — a non-reflexive equality (IEEE `Float`). Such a
    /// carrier is not a lawful `Eq` key, so the instantiation is a load error
    /// (`Map[K = Float]`), not a silent wrong answer. Use a lawful key type
    /// (`TotalFloat` for floats). Load-blocking.
    NonEqKeyRequiresLawfulEq {
        /// The parametric sort being instantiated (`anthill.prelude.Map`).
        container: String,
        /// The carrier bound where lawful `Eq` is required (`anthill.prelude.Float`).
        carrier: String,
    },
    /// WI-431 (rule 2 — COHERENCE): two or more DISTINCT instance facts (op-valued
    /// provisions, `fact Combiner[T = Tag, combine = combineA]` /
    /// `… combine = combineB]`) cover the same `(spec, carrier)`. Each supplies a
    /// different dictionary, and scoped/named instance selection is not yet
    /// implemented, so dispatch would silently pick the first (the
    /// `provider_spec_view_bindings` first-provider-wins contract). Load-blocking:
    /// the choice of implementation is ambiguous with no way to disambiguate.
    /// Keyed on the full canonical application (the WI-419 / §5.4 identity rule):
    /// identical instance facts hash-cons to one provision and are idempotent;
    /// only facts that differ (in carrier-or-op bindings) collide here. A
    /// type-only provision (`provides Stream[T = X]`, no op binding) supplies no
    /// dictionary and never participates.
    AmbiguousInstanceFact {
        carrier: String,
        spec: String,
        count: usize,
    },
    /// WI-450 witness coherence (rule 2, witness flavor): two distinct WITNESS
    /// SORTS provide one spec at the same application — `sort TagCombinerA provides
    /// Combiner[T = Tag]` and `sort TagCombinerB provides Combiner[T = Tag]`, each
    /// backing the spec's ops with its own member impls. Like two instance facts
    /// they give value-directed dispatch no sound choice (it would pick the first),
    /// but the conflict is between provider SORTS, not `fact` op-bindings — hence a
    /// distinct diagnostic. Load-blocking; keyed on (spec, dispatch carrier).
    AmbiguousWitness {
        carrier: String,
        spec: String,
        count: usize,
    },
    /// WI-347: an operation override violates behavioral subtyping — a
    /// carrier's own operation that implements/overrides a spec operation does
    /// not *refine* it. `reason` names the specific violation: an effect not
    /// covered by the spec's effects (effect-widening), a strengthened
    /// precondition, or a weakened postcondition. Load-blocking: the override
    /// is unsound — a caller programming against the spec's contract would be
    /// surprised.
    IncompatibleOverride {
        carrier: String,
        spec: String,
        op: String,
        reason: String,
    },
    /// WI-431 (B): an INSTANCE FACT binds a spec operation to an op whose
    /// SIGNATURE does not match the spec operation's, with the carrier substituted
    /// for the spec's type parameter — e.g. `fact Combiner[T = Tag, combine =
    /// wrongOp]` where `wrongOp` has the wrong arity or an unrelated param/return
    /// type. The bound op IS the dictionary entry dispatch now calls (WI-431
    /// increments 2/4), so a mis-typed binding would dispatch to a wrongly-typed
    /// impl. Load-blocking. Checked only when the substituted spec type and the
    /// bound type are both ground (a higher-kinded binding whose param stays
    /// parametric — `CpsMonad.pure : F[T = A]` — fails open, deferred to WI-383).
    IncompatibleInstanceBinding {
        carrier: String,
        spec: String,
        op: String,
        reason: String,
    },
    /// WI-431 (E): a parametric INSTANCE FACT (an op-valued provision, `fact
    /// CpsMonad[pure = …, flatMap = …]`) at namespace level binds operations but
    /// its CARRIER cannot be derived — the spec's first type parameter (the
    /// carrier slot, `carrier_param`) is not bound to a concrete sort/entity.
    /// Dispatch files and looks instances up BY carrier, so without one the whole
    /// instance — and its coverage / coherence / signature checks — would be
    /// silently dropped (the pre-(E) early-return). Load-blocking: a missing or
    /// mis-typed carrier binding must not quietly disable the instance.
    UnresolvableInstanceCarrier {
        spec: String,
        carrier_param: String,
    },
    Other {
        message: String,
    },
    /// WI-605: a bare `pattern -> body` in an expression position (an operation /
    /// const body). The infix `->` there builds an arrow-TYPE term, not a
    /// function value — so its left-hand binder names would load as unresolved
    /// value refs and cascade into misleading `UnresolvedName` typing errors.
    /// A lambda requires the `lambda` keyword (kernel-language.md §Lambda,
    /// proposal 018 — deliberate: the keyword keeps call-argument commas
    /// unambiguous). Load-blocking with the actionable hint instead of the
    /// cascade. Gated on pratt PROVENANCE (WI-618,
    /// `SimpleTermStore::is_minted`): only a desugared infix `->` fires;
    /// a user-written `arrow(a, b)` call keeps the normal path.
    ArrowTermInExprPosition {
        span: Span,
    },
    /// WI-618: a pratt-minted `pattern -> body` (the keyword-less lambda typo)
    /// in a rule (head or body) / fact / constraint / contract term position.
    /// Unlike an op/const body, an arrow-TYPE term is legitimate here (types
    /// are terms — e.g. a mapping fact carrying `Int -> Int`), so provenance
    /// alone cannot condemn the term; the discriminator is an unresolvable
    /// binder-looking (lowercase or `_`-led) LEAF name — one that can only
    /// have been meant as a lambda parameter (a real arrow type's leaves —
    /// sorts, type params, places — resolve, and its logical variables are
    /// `?`-vars, not bare names). Load-blocking: the clause would otherwise
    /// ride as inert data with unresolved leaves and silently never mean what
    /// was written. See `Loader::check_bare_arrow_typo` (also for the
    /// accepted false negatives: uppercase leaves, binder names that collide
    /// with in-scope names).
    BareArrowInLogicPosition {
        position: &'static str,
        unresolved: String,
        span: Span,
    },
    /// WI-023: an `aggregation` constraint (`count/sum/min/max(…) op bound`). The
    /// parser and loader carry it faithfully, but the guard engine cannot yet
    /// evaluate aggregation — so the loader reports it loudly (load-blocking)
    /// rather than registering a vacuously-true guard that would never fire.
    AggregationConstraintUnsupported {
        label: Option<String>,
        span: Span,
    },
    /// WI-023: a registered integrity constraint is violated by the loaded facts
    /// (the post-load `check_all_guards` pass). Load-blocking — the KB does not
    /// satisfy its own stated invariant.
    ConstraintViolated {
        label: Option<String>,
    },
    /// WI-513: a registered integrity constraint uses a `LogicalQuery` form the
    /// shared lowerer (`execute.rs::lower_query`) cannot handle — an unknown
    /// constructor (`disjunction`/`sort_query`/an aggregation/…) or a non-goal-
    /// shaped leaf. Surfaced loudly by the post-load `check_all_guards` pass.
    /// Load-BLOCKING: the constraint cannot be lowered to goals, so loading anyway
    /// would silently run with an unchecked invariant — the silent-skip the
    /// loud-error principle forbids. Carries the source label and lowering detail.
    ConstraintLoweringFailed {
        label: Option<String>,
        detail: String,
    },
    /// WI-628: a registered integrity constraint whose proof search TRUNCATED at
    /// the resolver depth limit — it can be neither confirmed nor refuted within
    /// budget, so it is neither cleanly `Violated` nor safely `Holds`.
    /// Load-BLOCKING: admitting the KB while a constraint's verdict was decided
    /// from an incomplete search is the unsoundness WI-628 closes. Distinct from
    /// `ConstraintLoweringFailed` (a malformed constraint FORM — here the form is
    /// fine, the SEARCH was cut short). Carries the source label and a reason.
    ConstraintUndecidable {
        label: Option<String>,
        detail: String,
    },
    /// WI-023: a constraint uses a form the guard engine cannot yet enforce
    /// CORRECTLY — e.g. a `forall` with a multi-atom / nested `-:` body (whose
    /// negation needs `¬(Q1 ∧ Q2)`, which the per-goal negation can't express).
    /// Reported loudly (load-blocking) rather than registered as a guard that
    /// would silently mis-evaluate.
    UnsupportedConstraintForm {
        label: Option<String>,
        detail: String,
        span: Span,
    },
    /// WI-366: a value-in-type binding (a denoted value like `Vector[Int64, 3]`, or
    /// a `Modify[c]` effect row) in a sort-relation position (`sort T = …`, a
    /// `requires` / `provides` spec). It rides faithfully as a `Value::Node` fact,
    /// but RESOLVING it (alias expansion, requires/provides dispatch and coverage)
    /// is gated on effect-expressions-as-types and not yet implemented — so the
    /// loader rejects it (load-blocking) rather than silently accepting an
    /// unenforced / unresolved clause.
    ValueInTypeNotResolved {
        position: &'static str,
        name: String,
    },
    /// WI-440: an unresolved name inside a `-E` effect-absence label
    /// (`-Modify[zzz]` with no such binder/value in scope). Load-BLOCKING —
    /// the declared lacks-constraint would be VACUOUS (nothing could ever
    /// match the place), so a typo would silently disable the check the
    /// author wrote.
    UnresolvedEffectPlace {
        name: String,
    },
    /// WI-429: an unresolvable Capitalized dotted name in TYPE position.
    /// Previously this fell through to `remap_name`'s advisory
    /// `UnresolvedName` and minted a degenerate nominal sort literally named
    /// e.g. `"Storage.Key"` — false-rejecting valid programs (the nominal
    /// matches nothing) and false-accepting invalid ones (two such positions
    /// conflate to one meaningless global nominal). Load-blocking.
    UnresolvedTypeName {
        name: String,
        span: Span,
        scope_name: String,
    },
    /// WI-709: a sort application's type ARGUMENTS do not fit the sort's declared type
    /// params — a named argument keys a param the sort never declares (`Cell[W = Int64]`;
    /// `Cell` declares only `V`), or a positional has no declared param left to bind
    /// (`Cell[Int64, String]`). This is the TYPE-position (written) face of
    /// [`crate::kb::TypeArgProblem`]; `TypeError::InvalidTypeArgument` is the
    /// VALUE-position (WI-707, `is_modifiable(Cell[W = Int64])`) one, and both decide it
    /// with the same [`KnowledgeBase::check_sort_type_args`] — so one written type cannot
    /// mean two things depending on where it appears. Load-blocking: the stray binding
    /// was previously kept in the type term (in type position) or dropped (an
    /// over-applied positional), and either way the type silently meant something other
    /// than what was written.
    InvalidTypeArgument {
        detail: String,
        span: Option<Span>,
    },
    /// WI-489: a value-in-type field projection (`Modify[result.nonexistent]`,
    /// `Modify[c.bogus]`) names a field the head's statically-known CONCRETE type
    /// (an entity / named-tuple param or `result`) does not declare. The v1 denoted
    /// place interns field names raw and defers resolution to the elimination/eval
    /// site, so without this the bogus field would be silently accepted at load.
    /// Load-blocking: the projected resource/type names nothing. `path` is the full
    /// projection up to and including the bad field; `type_display` the type that
    /// lacks it.
    InvalidFieldProjection {
        path: String,
        field: String,
        type_display: String,
        span: Span,
    },
    /// WI-369: a cross-scope reference to a name declared `internal` — a
    /// constructor, sort, or operation that is "hidden from outside the
    /// declaring scope" (kernel-language.md §8.6). The name resolves to a real
    /// internal symbol, but the referencing scope is neither its declaring scope
    /// nor a lexical descendant, so the reference is forbidden. Load-blocking:
    /// `internal` exists to encapsulate stateful carriers (a `MutableStack`'s
    /// `rep` cell), so silently allowing the alias would defeat the guarantee.
    ForbiddenInternalAccess {
        name: String,
        declared_in: String,
        scope_name: String,
        span: Span,
    },
    /// WI-525 (proposal 049, NAF discipline): a `<=>` (unify) goal occurs under
    /// `not(...)` in a rule body with a variable that no EARLIER positive goal
    /// binds. `<=>` BINDS, and NAF on a non-ground goal is unsound — so a
    /// negated unify whose variables aren't range-restricted by a preceding
    /// positive goal would flounder (delay forever) or silently mis-behave.
    /// Load-blocking ("know errors early"); the undischarged-residual honesty
    /// backstop (WI-519) is the runtime fallback. EVERY variable counts,
    /// including the anonymous `?`: anthill's NAF requires a GROUND inner goal
    /// (`step_naf` delays otherwise), so an unbound var on either side of the
    /// unify makes `not` flounder — the Prolog "x is not of shape `f(_)`" idiom
    /// genuinely does not work soundly here.
    UnsafeNegatedUnify {
        var_name: String,
        span: Span,
    },
    /// WI-525 (proposal 049, NAF discipline): a BINDING `<=>` / `let` goal (both
    /// lower to `unify(?v, e)`) appears in a contract position — an operation
    /// `requires` / `ensures` clause, or a `constraint` body. Contracts TEST
    /// (`=`), they must never BIND: a postcondition that binds a fresh variable
    /// is not a verifiable claim. Load-blocking — use `=` (a test) instead. A
    /// `unify` under `not(...)` is a TEST (NAF), not a binding, so it is not
    /// flagged here.
    BindingInContract {
        /// `"requires"` / `"ensures"` / `"constraint"`.
        position: String,
        span: Span,
    },
}

impl LoadError {
    /// Format with line:col using source text, like ParseError::format_with_source.
    pub fn format_with_source(&self, source: &str) -> String {
        match self {
            LoadError::UnresolvedName { name, span, scope_name } => {
                let (line, col) = Span::line_col(source, span.start);
                format!("{}:{}: unresolved name '{}' in scope '{}'", line, col, name, scope_name)
            }
            LoadError::UnresolvedImport { path, span } => {
                let (line, col) = Span::line_col(source, span.start);
                format!("{}:{}: unresolved import '{}'", line, col, path)
            }
            LoadError::AmbiguousSymbol { name, candidates, span, scope_name } => {
                let (line, col) = Span::line_col(source, span.start);
                format!("{}:{}: ambiguous symbol '{}' in scope '{}': candidates {:?}", line, col, name, scope_name, candidates)
            }
            LoadError::TypeMismatch { entity_name, field_name, expected_type, actual_type, span, origin } => {
                let tag = type_mismatch_tag(origin);
                let site = type_mismatch_origin_suffix(origin);
                if let Some(sp) = span {
                    let (line, col) = Span::line_col(source, sp.start);
                    format!("{}:{}: type mismatch in {}.{}{}: expected {}, got {}{}", line, col, entity_name, field_name, tag, expected_type, actual_type, site)
                } else {
                    format!("type mismatch in {}.{}{}: expected {}, got {}{}", entity_name, field_name, tag, expected_type, actual_type, site)
                }
            }
            LoadError::UnsatisfiedProviderRequires { carrier, spec, required } => {
                format!("'{}' provides '{}', which requires '{}', but '{}' does not provide '{}' (add a `fact {}[…]` for the carrier)",
                    carrier, spec, required, carrier, required, required)
            }
            LoadError::UnbackedProviderOperation { carrier, spec, op } => {
                format!("'{}' provides '{}' but does not back operation '{}.{}': there is no default on '{}' (an `operation {}(…) = …` body or a derivation rule) and '{}' supplies no own '{}' (add a body/rule on '{}' or an `operation {}(…)` on '{}')",
                    carrier, spec, spec, op, spec, op, carrier, op, spec, op, carrier)
            }
            LoadError::IncompatibleEqNonEq { carrier } => {
                format!("'{}' provides both 'Eq' and 'NonEq', which are mutually exclusive: a carrier's `eq` cannot be both lawful (reflexive) and non-reflexive. A partial carrier (e.g. IEEE Float) provides PartialEq + NonEq; a lawful carrier provides PartialEq + Eq — drop whichever is wrong.",
                    carrier)
            }
            LoadError::NonEqKeyRequiresLawfulEq { container, carrier } => {
                format!("'{}' requires a lawful `Eq` key, but '{}' provides `NonEq` (its equality is not reflexive — e.g. IEEE `nan != nan`), so it cannot be a lawful key. Use a lawful key type (`TotalFloat` for floats) instead of '{}'.",
                    container, carrier, carrier)
            }
            LoadError::AmbiguousInstanceFact { carrier, spec, count } => {
                format!("ambiguous instance: {} distinct instance facts provide '{}' for carrier '{}' — each binds the spec's operations differently, and there is no way to select between them (scoped/named instance selection is not yet supported); keep exactly one `fact {}[…]` per (spec, carrier)",
                    count, spec, carrier, spec)
            }
            LoadError::AmbiguousWitness { carrier, spec, count } => {
                format!("ambiguous witness: {} distinct witness sorts provide '{}' for carrier '{}' — each backs the spec's operations with its own member ops, and there is no way to select between them (scoped/named instance selection is not yet supported); keep exactly one `sort … provides {}[…]` witness per (spec, carrier)",
                    count, spec, carrier, spec)
            }
            LoadError::IncompatibleOverride { carrier, spec, op, reason } => {
                format!("'{}' overrides '{}.{}' (it provides '{}') but the override does not refine it: {}",
                    carrier, spec, op, spec, reason)
            }
            LoadError::IncompatibleInstanceBinding { carrier, spec, op, reason } => {
                format!("instance fact `{}[…]` binds operation '{}.{}' to an operation whose signature does not match (with '{}' substituted for the spec's type parameter): {}",
                    spec, spec, op, carrier, reason)
            }
            LoadError::UnresolvableInstanceCarrier { spec, carrier_param } => {
                format!("instance fact `{}[…]` binds operations but its carrier cannot be derived: the carrier type parameter '{}' is not bound to a concrete sort (write `fact {}[{} = SomeSort, …]`)",
                    spec, carrier_param, spec, carrier_param)
            }
            LoadError::Other { message } => {
                format!("load error: {}", message)
            }
            LoadError::ArrowTermInExprPosition { span } => {
                let (line, col) = Span::line_col(source, span.start);
                format!("{}:{}: {}", line, col, arrow_expr_hint())
            }
            LoadError::BareArrowInLogicPosition { position, unresolved, span } => {
                let (line, col) = Span::line_col(source, span.start);
                format!("{}:{}: {}", line, col, bare_arrow_logic_msg(position, unresolved))
            }
            LoadError::AggregationConstraintUnsupported { label, span } => {
                let (line, col) = Span::line_col(source, span.start);
                format!("{}:{}: aggregation constraint{} is not yet enforced (the guard engine cannot evaluate count/sum/min/max)",
                    line, col, label_suffix(label))
            }
            LoadError::ConstraintViolated { label } => {
                format!("integrity constraint{} is violated by the loaded facts", label_suffix(label))
            }
            LoadError::ConstraintLoweringFailed { label, detail } => {
                format!(
                    "integrity constraint{} uses a LogicalQuery form the resolver cannot lower: {}",
                    label_suffix(label), detail,
                )
            }
            LoadError::ConstraintUndecidable { label, detail } => {
                format!(
                    "integrity constraint{} is undecidable within the resolver depth budget: {}",
                    label_suffix(label), detail,
                )
            }
            LoadError::UnsupportedConstraintForm { label, detail, span } => {
                let (line, col) = Span::line_col(source, span.start);
                format!("{}:{}: constraint{} uses an unsupported form: {}", line, col, label_suffix(label), detail)
            }
            LoadError::ValueInTypeNotResolved { position, name } => {
                format!(
                    "value-in-type binding in {} (`{}[…]`) is not yet resolved \
                     (gated on effect-expressions-as-types)",
                    position, name,
                )
            }
            LoadError::UnresolvedEffectPlace { name } => {
                format!(
                    "unresolved place `{}` in a `-…` effect-absence label — \
                     the lacks-constraint would be vacuous",
                    name,
                )
            }
            LoadError::UnresolvedTypeName { name, span, scope_name } => {
                let (line, col) = Span::line_col(source, span.start);
                format!(
                    "{}:{}: unresolved type name '{}' in scope '{}' — not a value \
                     projection (`s.Member` off a param/local/field), not a \
                     type-parameter or sort projection (`P.Member` / `Sort.Member`), \
                     and not a resolvable qualified sort reference",
                    line, col, name, scope_name,
                )
            }
            LoadError::InvalidTypeArgument { detail, span } => match span {
                Some(sp) => {
                    let (line, col) = Span::line_col(source, sp.start);
                    format!("{}:{}: invalid type argument: {}", line, col, detail)
                }
                None => format!("invalid type argument: {}", detail),
            },
            LoadError::InvalidFieldProjection { path, field, type_display, span } => {
                let (line, col) = Span::line_col(source, span.start);
                format!(
                    "{}:{}: field projection '{}': {} has no field '{}'",
                    line, col, path, type_display, field,
                )
            }
            LoadError::ForbiddenInternalAccess { name, declared_in, scope_name, span } => {
                let (line, col) = Span::line_col(source, span.start);
                format!(
                    "{}:{}: '{}' is internal to '{}' and cannot be referenced from scope '{}'",
                    line, col, name, declared_in, scope_name,
                )
            }
            LoadError::UnsafeNegatedUnify { var_name, span } => {
                let (line, col) = Span::line_col(source, span.start);
                format!(
                    "{}:{}: variable '{}' in a `<=>` (unify) under `not` is not bound by \
                     an earlier positive goal — negation-as-failure on an unbound \
                     unification is unsound; bind it positively first",
                    line, col, var_name,
                )
            }
            LoadError::BindingInContract { position, span } => {
                let (line, col) = Span::line_col(source, span.start);
                format!(
                    "{}:{}: a binding `<=>` / `let` is not allowed in a {} contract — \
                     contracts must TEST, not bind; use `=` (equality test) instead",
                    line, col, position,
                )
            }
        }
    }

    /// Errors that block load — execution must not proceed:
    /// - `TypeMismatch`: ill-typed program is unsound.
    /// - `UnresolvedImport`: imported names won't bind a local alias, so
    ///   any use-site that refers to them by short name relies on
    ///   accidental scope walks; better to fail at load time than silently
    ///   resolve to the wrong (or no) symbol.
    pub fn is_load_blocking(&self) -> bool {
        matches!(self,
            LoadError::TypeMismatch { .. }
            | LoadError::UnresolvedImport { .. }
            | LoadError::UnsatisfiedProviderRequires { .. }
            | LoadError::UnbackedProviderOperation { .. }
            // WI-658: a carrier providing both Eq and NonEq is contradictory.
            | LoadError::IncompatibleEqNonEq { .. }
            // WI-644: a NonEq carrier can't be a lawful `Eq` key (`Map[K=Float]`).
            | LoadError::NonEqKeyRequiresLawfulEq { .. }
            // WI-431 rule 2: ambiguous instance facts give dispatch no sound
            // choice — block rather than silently pick the first. WI-450: the
            // witness flavor (two provider sorts) is equally unsound.
            | LoadError::AmbiguousInstanceFact { .. }
            | LoadError::AmbiguousWitness { .. }
            | LoadError::IncompatibleOverride { .. }
            // WI-431 (B): a mis-typed instance-fact op binding would dispatch to
            // a wrongly-typed impl — block.
            | LoadError::IncompatibleInstanceBinding { .. }
            // WI-431 (E): an op-bearing instance fact whose carrier cannot be
            // derived would be silently dropped — block instead.
            | LoadError::UnresolvableInstanceCarrier { .. }
            // WI-366: a value-in-type in a sort-relation position is not yet
            // resolvable — fail loudly rather than run with an unenforced clause.
            | LoadError::ValueInTypeNotResolved { .. }
            // WI-440: a typo'd place in a `-…` absence label = vacuous constraint.
            | LoadError::UnresolvedEffectPlace { .. }
            // WI-429: an unresolvable Capitalized dotted name in type position
            // would otherwise load as a degenerate nominal sort.
            | LoadError::UnresolvedTypeName { .. }
            // WI-489: a value-in-type field projection onto a non-existent field
            // names nothing — block rather than defer to a silent accept.
            | LoadError::InvalidFieldProjection { .. }
            // WI-709: a type argument the sort never declared (or one positional too
            // many) makes the written type mean something other than what it says —
            // and made the type- and value-position spellings of it disagree.
            | LoadError::InvalidTypeArgument { .. }
            // WI-369: a cross-scope reference to an `internal` name defeats the
            // encapsulation it was declared for — block.
            | LoadError::ForbiddenInternalAccess { .. }
            // WI-525 (proposal 049): an unsound negated unify and a binding
            // unify in a contract are both load-time NAF/contract-discipline
            // violations — block ("know errors early").
            | LoadError::UnsafeNegatedUnify { .. }
            | LoadError::BindingInContract { .. }
            // WI-605: a bare `pattern -> body` where a lambda was meant — the
            // body's binder names resolve to nothing, so the operation cannot
            // mean what was written.
            | LoadError::ArrowTermInExprPosition { .. }
            // WI-618: the same typo in a rule-body / constraint / contract
            // position — the clause cannot mean what was written.
            | LoadError::BareArrowInLogicPosition { .. }
            // WI-023: an unenforceable aggregation constraint and a violated
            // integrity constraint are both unsound to run with.
            | LoadError::AggregationConstraintUnsupported { .. }
            | LoadError::ConstraintViolated { .. }
            | LoadError::ConstraintLoweringFailed { .. }
            // WI-628: a constraint decided from a truncated (incomplete) search
            // is unsound to run with — block rather than pass silently.
            | LoadError::ConstraintUndecidable { .. }
            | LoadError::UnsupportedConstraintForm { .. })
    }
}

/// WI-605/WI-618: the one actionable tail shared by both bare-arrow
/// diagnostics, so their advice cannot drift apart.
const LAMBDA_KEYWORD_HINT: &str =
    "a lambda needs the `lambda` keyword (e.g. `lambda (x, y) -> body`)";

/// WI-605: the one hint text for `ArrowTermInExprPosition`, shared by both
/// renderings (`format_with_source` and `Display`) so the wording cannot drift.
fn arrow_expr_hint() -> String {
    format!(
        "`->` in expression position builds an arrow-type term, not a function \
         value — {LAMBDA_KEYWORD_HINT}"
    )
}

/// WI-618: the one message body for `BareArrowInLogicPosition`, shared by both
/// renderings (`format_with_source` and `Display`) so the wording cannot drift.
/// "does not resolve" covers both `NotFound` and `Ambiguous` — either way the
/// name fails to resolve to a single referent.
fn bare_arrow_logic_msg(position: &str, unresolved: &str) -> String {
    format!(
        "in {position}: `->` builds an arrow-type term, but `{unresolved}` \
         does not resolve in scope — if a function value was meant, \
         {LAMBDA_KEYWORD_HINT}"
    )
}

/// WI-618: binder-introducing parse forms the bare-arrow walks must scope —
/// the pattern child's names bind in the later children, mirroring the scope
/// pushes of the op-body load walk (`visit_load`). Returns
/// `(pattern_idx, first_scoped_idx)`: `lambda_expr(pat, body)` and
/// `match_branch(pat, body, guard?)` scope everything after the pattern;
/// `let_expr(pat, value, body)` scopes only the body — the value sees the
/// OUTER scope.
fn binder_form_layout(name: &str) -> Option<(usize, usize)> {
    match name {
        "lambda_expr" | "match_branch" => Some((0, 1)),
        "let_expr" => Some((0, 2)),
        _ => None,
    }
}

/// Render a constraint label as ` 'label'` for diagnostics, or `""` if unlabeled.
pub(crate) fn label_suffix(label: &Option<String>) -> String {
    match label {
        Some(l) => format!(" '{l}'"),
        None => String::new(),
    }
}

/// WI-525 (proposal 049, Part A): walk a `not(...)` body occurrence and record,
/// for every `<=>` (unify) goal nested anywhere beneath it, each variable not in
/// `bound` (the set of vars range-restricted by earlier positive goals). A `not`
/// may wrap a compound (`not(conjunction(...))`) or another `not`, so the whole
/// subtree is scanned; nested `not` nodes are transparent (an inner unify is
/// still under negation). EVERY variable counts — including the anonymous `?`
/// (interned as `"_"`): anthill's NAF requires a ground inner goal, so an unbound
/// var on either side floounders the `not` regardless of how it is spelled (and a
/// named `?_` is interned to `"_"` too, so a name test could not distinguish the
/// two anyway).
fn collect_negated_unify_violations(
    kb: &KnowledgeBase,
    not_node: &Rc<NodeOccurrence>,
    bound: &HashSet<u32>,
    out: &mut Vec<(String, Span)>,
) {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(not_node)];
    // One diagnostic per offending variable across this `not`.
    let mut reported: HashSet<u32> = HashSet::new();
    while let Some(occ) = stack.pop() {
        if kb.get_builtin_view(&occ) == Some(BuiltinTag::Unify) {
            let mut vars = Vec::new();
            let mut seen = HashSet::new();
            node_occurrence::collect_occurrence_global_vars(&occ, &mut vars, &mut seen);
            for v in vars {
                if !bound.contains(&v.raw()) && reported.insert(v.raw()) {
                    out.push((kb.symbols.name(v.name()).to_string(), occ.span.span));
                }
            }
        }
        if let node_occurrence::NodeKind::Expr { expr, .. } = &occ.kind {
            node_occurrence::for_each_child(expr, |c| stack.push(Rc::clone(c)));
        }
    }
}

/// WI-525 (proposal 049, Part B): collect every goal `TermId` appearing in a
/// constraint body, across all forms (denial head + guard, quantified condition
/// + nested body, leaf patterns, aggregation condition + body). Each is a
/// candidate contract goal the binding-unify check classifies.
fn collect_constraint_body_goal_tids(body: &ConstraintBody, out: &mut Vec<TermId>) {
    match body {
        ConstraintBody::Denial { head, guard } => {
            out.extend(head.iter().copied());
            if let Some(g) = guard {
                out.extend(g.iter().copied());
            }
        }
        ConstraintBody::Quantified { condition, body, .. } => {
            out.extend(condition.iter().copied());
            collect_constraint_body_goal_tids(body, out);
        }
        ConstraintBody::Patterns(p) => out.extend(p.iter().copied()),
        ConstraintBody::Aggregation { condition, body, .. } => {
            out.extend(condition.iter().copied());
            out.extend(body.iter().copied());
        }
    }
}

/// WI-023: a quantifier body the guard evaluator cannot enforce CORRECTLY, with a
/// human detail; `None` if the form is supported. Two cases: (1) a `forall` whose
/// `-:` body is not a single pattern — its negation needs `¬(Q1 ∧ Q2)`, which the
/// per-goal negation can't express (it would compute `¬Q1 ∧ ¬Q2`); (2) ANY
/// quantifier with a NESTED quantified/aggregation body — `lower_logical_query`
/// only lowers a pattern conjunction, so a nested quantifier would be treated as a
/// single opaque goal. Pattern-conjunction bodies of `no`/`some`/`one`/`lone` are
/// fine.
fn unsupported_quantifier_form(body: &ConstraintBody) -> Option<String> {
    let ConstraintBody::Quantified { quantifier, body, .. } = body else {
        return None;
    };
    match body.as_ref() {
        ConstraintBody::Patterns(v) => {
            if *quantifier == Quantifier::Forall && v.len() != 1 {
                Some("`forall` with a multi-atom `-:` body is not yet supported \
                      (its negation needs ¬(Q1 ∧ Q2)); use a single body atom or \
                      split into separate constraints".to_string())
            } else {
                None
            }
        }
        _ => Some("a quantifier with a nested quantified/aggregation `-:` body is \
                   not yet supported".to_string()),
    }
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::UnresolvedName { name, span, scope_name } => {
                write!(f, "unresolved name '{}' in scope '{}' at {}..{}", name, scope_name, span.start, span.end)
            }
            LoadError::UnresolvedImport { path, span } => {
                write!(f, "unresolved import '{}' at {}..{}", path, span.start, span.end)
            }
            LoadError::AmbiguousSymbol { name, candidates, span, scope_name } => {
                write!(f, "ambiguous symbol '{}' in scope '{}' at {}..{}: candidates {:?}", name, scope_name, span.start, span.end, candidates)
            }
            LoadError::TypeMismatch { entity_name, field_name, expected_type, actual_type, span, origin } => {
                let tag = type_mismatch_tag(origin);
                let site = type_mismatch_origin_suffix(origin);
                if let Some(sp) = span {
                    write!(f, "type mismatch in {}.{}{}: expected {}, got {}{} at {}..{}", entity_name, field_name, tag, expected_type, actual_type, site, sp.start, sp.end)
                } else {
                    write!(f, "type mismatch in {}.{}{}: expected {}, got {}{}", entity_name, field_name, tag, expected_type, actual_type, site)
                }
            }
            LoadError::UnsatisfiedProviderRequires { carrier, spec, required } => {
                write!(f, "'{}' provides '{}', which requires '{}', but '{}' does not provide '{}'",
                    carrier, spec, required, carrier, required)
            }
            LoadError::UnbackedProviderOperation { carrier, spec, op } => {
                write!(f, "'{}' provides '{}' but backs no operation '{}.{}' (no default on '{}', no own '{}' on '{}')",
                    carrier, spec, spec, op, spec, op, carrier)
            }
            LoadError::IncompatibleEqNonEq { carrier } => {
                write!(f, "'{}' provides both 'Eq' and 'NonEq', which are mutually exclusive (a partial carrier provides PartialEq + NonEq; a lawful one PartialEq + Eq)",
                    carrier)
            }
            LoadError::NonEqKeyRequiresLawfulEq { container, carrier } => {
                write!(f, "'{}' requires a lawful `Eq` key, but '{}' provides `NonEq` (non-reflexive equality) — not a lawful key; use `TotalFloat` for floats",
                    container, carrier)
            }
            LoadError::AmbiguousInstanceFact { carrier, spec, count } => {
                write!(f, "ambiguous instance: {} distinct instance facts provide '{}' for carrier '{}' (keep exactly one)",
                    count, spec, carrier)
            }
            LoadError::AmbiguousWitness { carrier, spec, count } => {
                write!(f, "ambiguous witness: {} distinct witness sorts provide '{}' for carrier '{}' (keep exactly one)",
                    count, spec, carrier)
            }
            LoadError::IncompatibleOverride { carrier, spec, op, reason } => {
                write!(f, "'{}' overrides '{}.{}' but does not refine it: {}", carrier, spec, op, reason)
            }
            LoadError::IncompatibleInstanceBinding { carrier, spec, op, reason } => {
                write!(f, "instance fact '{}' binds '{}.{}' to a signature-incompatible operation (carrier '{}'): {}", spec, spec, op, carrier, reason)
            }
            LoadError::UnresolvableInstanceCarrier { spec, carrier_param } => {
                write!(f, "instance fact '{}' binds operations but its carrier ('{}') is not bound to a sort", spec, carrier_param)
            }
            LoadError::Other { message } => {
                write!(f, "load error: {}", message)
            }
            LoadError::ArrowTermInExprPosition { span } => {
                write!(f, "{} at {}..{}", arrow_expr_hint(), span.start, span.end)
            }
            LoadError::BareArrowInLogicPosition { position, unresolved, span } => {
                write!(f, "{} at {}..{}",
                    bare_arrow_logic_msg(position, unresolved), span.start, span.end)
            }
            LoadError::AggregationConstraintUnsupported { label, span } => {
                write!(f, "aggregation constraint{} is not yet enforced at {}..{}", label_suffix(label), span.start, span.end)
            }
            LoadError::ConstraintViolated { label } => {
                write!(f, "integrity constraint{} is violated by the loaded facts", label_suffix(label))
            }
            LoadError::ConstraintLoweringFailed { label, detail } => {
                write!(f, "integrity constraint{} uses a LogicalQuery form the resolver cannot lower: {}", label_suffix(label), detail)
            }
            LoadError::ConstraintUndecidable { label, detail } => {
                write!(f, "integrity constraint{} is undecidable within the resolver depth budget: {}", label_suffix(label), detail)
            }
            LoadError::UnsupportedConstraintForm { label, detail, span } => {
                write!(f, "constraint{} uses an unsupported form ({}) at {}..{}", label_suffix(label), detail, span.start, span.end)
            }
            LoadError::ValueInTypeNotResolved { position, name } => {
                write!(
                    f,
                    "value-in-type binding in {position} (`{name}[…]`) is not yet \
                     resolved (gated on effect-expressions-as-types)"
                )
            }
            LoadError::UnresolvedEffectPlace { name } => {
                write!(
                    f,
                    "unresolved place `{name}` in a `-…` effect-absence label — \
                     the lacks-constraint would be vacuous"
                )
            }
            LoadError::UnresolvedTypeName { name, span, scope_name } => {
                write!(
                    f,
                    "unresolved type name '{}' in scope '{}' at {}..{} — not a value \
                     projection (`s.Member` off a param/local/field), not a \
                     type-parameter or sort projection (`P.Member` / `Sort.Member`), \
                     and not a resolvable qualified sort reference",
                    name, scope_name, span.start, span.end,
                )
            }
            LoadError::InvalidTypeArgument { detail, span } => match span {
                Some(sp) => {
                    write!(f, "invalid type argument at {}..{}: {}", sp.start, sp.end, detail)
                }
                None => write!(f, "invalid type argument: {}", detail),
            },
            LoadError::InvalidFieldProjection { path, field, type_display, span } => {
                write!(
                    f,
                    "field projection '{}' at {}..{}: {} has no field '{}'",
                    path, span.start, span.end, type_display, field,
                )
            }
            LoadError::ForbiddenInternalAccess { name, declared_in, scope_name, span } => {
                write!(
                    f,
                    "'{}' is internal to '{}' and cannot be referenced from scope '{}' at {}..{}",
                    name, declared_in, scope_name, span.start, span.end,
                )
            }
            LoadError::UnsafeNegatedUnify { var_name, span } => {
                write!(
                    f,
                    "variable '{}' in a `<=>` (unify) under `not` is not bound by an \
                     earlier positive goal (unsound NAF) at {}..{}",
                    var_name, span.start, span.end,
                )
            }
            LoadError::BindingInContract { position, span } => {
                write!(
                    f,
                    "a binding `<=>` / `let` is not allowed in a {} contract \
                     (contracts test, not bind; use `=`) at {}..{}",
                    position, span.start, span.end,
                )
            }
        }
    }
}

/// A non-fatal load diagnostic (WI-345). Parallel to [`LoadError`], but
/// advisory: emitting one does **not** fail the load. Surfaced via
/// [`LoadResult::warnings`] so lint-style passes can report findings that
/// are legal-but-suspicious (e.g. the WI-346 requires-shadow) without
/// blocking the program. Kept a distinct type — not a non-blocking
/// `LoadError` — so "the load failed" and "the load has advice" never get
/// conflated.
#[derive(Clone, Debug)]
pub enum LoadWarning {
    /// Open-ended advisory message.
    Other { message: String },
    /// WI-346: a sort that `requires` a spec declares a local operation whose
    /// short name shadows one of that spec's own operations. The two are
    /// distinct, unrelated symbols — `requires` never overrides (override is
    /// the `provides` direction) — so this is legal but usually a mistake
    /// (the author meant to override). Skipped when the sort also *provides*
    /// the spec, where the own op IS a legitimate override.
    RequiresShadow {
        /// Qualified name of the sort declaring the shadowing op.
        sort: String,
        /// Short name of the shadowed (and shadowing) operation.
        op: String,
        /// Qualified name of the required spec that also declares `op`.
        spec: String,
    },
}

impl LoadWarning {
    /// Format with `line:col` using source text, parallel to
    /// [`LoadError::format_with_source`]. Variants that carry a span will
    /// resolve a location here; the current span-less `Other` ignores
    /// `source` and renders the bare message.
    pub fn format_with_source(&self, source: &str) -> String {
        let _ = source; // reserved for span-bearing variants (WI-346)
        self.to_string()
    }
}

impl std::fmt::Display for LoadWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadWarning::Other { message } => write!(f, "warning: {}", message),
            LoadWarning::RequiresShadow { sort, op, spec } => write!(f,
                "warning: operation `{op}` in `{sort}` shadows the inherited `{spec}.{op}` \
                 (`{sort}` requires `{spec}`); `requires` does not override — the two are \
                 distinct operations. Qualify `{spec}.{op}` to call the inherited one, or \
                 rename `{op}` to silence."),
        }
    }
}

impl std::error::Error for LoadError {}

// ══════════════════════════════════════════════════════════════════
// Phase 1: Scan definitions
// ══════════════════════════════════════════════════════════════════
// Phase 1: Scan definitions
// ══════════════════════════════════════════════════════════════════

/// Scan all parsed files to define symbols (sorts, namespaces, entities,
/// operations, rules) and build the scope inclusion chain (requires, imports).
///
/// Four sub-passes over all files:
/// - Pass 1: Define all names, record exposed variants and type params
/// - Pass 2: Process `requires` and `import` declarations → build parent scope chain
/// - Pass 3: Register unlabeled rule head-functor Goals (proposal 044 / B2)
/// - Pass 4: Retry deferred cross-namespace predicate imports (WI-295)
///
/// INVARIANT (WI-321) — cross-file mutual structural recursion is SUPPORTED.
/// Pass 1 defines EVERY name across EVERY file before ANY pass 2 runs, so two
/// files whose sorts/entities reference each other (`a.anthill` has `entity
/// Node(child: B)` while `b.anthill` has `entity Leaf(parent: A)`, plus a mutual
/// `import` cycle) BOTH load: each file's pass 1 ignores the other's content, so
/// both names exist before either file's imports/field-types resolve. This is
/// the standard "collect all top-level names, then resolve bodies" technique
/// (cf. SML/Haskell mutual recursion) — deliberate, not incidental. It is
/// LOAD-BEARING: a future single-pass / streaming loader, or imports evolving to
/// carry pass-1-needed info, must preserve the "all pass 1, then all pass 2"
/// ordering or the cycle deadlocks. Pinned by
/// `wi321_cross_file_mutual_recursion_test`.
pub fn scan_definitions(kb: &mut KnowledgeBase, files: &[&ParsedFile]) -> Vec<LoadError> {
    let global = kb.make_name_term("_global");

    // Sub-pass 1: define all names
    for file in files {
        scan_items_pass1(kb, &file.items, &file.symbols, &file.terms, global, "");
    }

    // Sub-pass 2: process requires and imports (all sorts exist now). A
    // Selective import of a rule-defined predicate can't resolve here — its
    // head-functor Goal isn't registered until sub-pass 3 — so such names are
    // deferred into `pending` and retried below (WI-295).
    let mut errors = Vec::new();
    let mut pending: Vec<PendingImport> = Vec::new();
    for file in files {
        scan_items_pass2(kb, &file.items, &file.symbols, global, "", &mut errors, &mut pending);
    }

    // Sub-pass 3: register unlabeled rule head-functor Goals, binding to an
    // inherited/existing origin where one resolves (proposal 044 / B2).
    for file in files {
        scan_items_pass3(kb, &file.items, &file.symbols, &file.terms, global, "");
    }

    // Sub-pass 4 (WI-295): retry deferred predicate imports. Head-functor Goals
    // from sub-pass 3 are now in `by_qualified_name`, so a cross-namespace
    // rule-predicate import resolves like any declared name. (Resolve by
    // symbol, not `rules_by_functor` — rules aren't asserted until the load phase.)
    for p in pending {
        match kb.symbols.by_qualified_name.get(&p.qualified).copied() {
            Some(sym) => kb.symbols.add_import(p.scope_raw, &p.short, sym),
            None => errors.push(LoadError::UnresolvedImport { path: p.qualified, span: p.span }),
        }
    }

    // WI-040: the kernel DESUGARING VOCAB (reflect `Expr` / `Pattern`
    // constructors, `field_access`, literal carriers, reflection primitives) is
    // NOT global-imported. It resolves directly to its reserved qualified home
    // via `kernel_vocab_qualified` in `remap_name_str`, so it never enters the
    // user name namespace — dissolving the collision blocklist WI-476 needed.
    errors
}

/// WI-040: fully-qualified KERNEL DESUGARING NAMES that the converter / loader
/// SYNTHESIZE into bodies (for `match` / `if` / `let` / `lambda`, member access,
/// literals, patterns) but a user never writes. These are RESERVED: a bare
/// reference resolves directly to the qualified target here (see
/// `kernel_vocab_qualified`), NOT through a `_global` import — so they never sit
/// in the user name namespace and need no collision blocklist. Resolution is a
/// fallback (reached only when the name is unresolvable in scope), so a
/// user-written same-spelling name still wins. Reflect-API names that ARE
/// plausible user definitions (`kind`, `fields`, `rules`, `kb`, `constructor`,
/// `not`) are deliberately NOT in this list — they are not converter-synthesized
/// and resolve via explicit import.
const KERNEL_VOCAB_QUALIFIED: &[&str] = &[
    // reflect.Expr constructors (synthetic `match` / `if` / `let` / `lambda`
    // and higher-order / dotted application + literals)
    "anthill.reflect.Expr.match_expr",
    "anthill.reflect.Expr.if_expr",
    "anthill.reflect.Expr.let_expr",
    "anthill.reflect.Expr.lambda_expr",
    "anthill.reflect.Expr.ho_apply",
    "anthill.reflect.Expr.dot_apply",
    "anthill.reflect.Expr.var_ref",
    "anthill.reflect.Expr.int_lit",
    "anthill.reflect.Expr.bigint_lit",
    "anthill.reflect.Expr.float_lit",
    "anthill.reflect.Expr.string_lit",
    "anthill.reflect.Expr.bool_lit",
    // reflect.Pattern constructors (synthetic match/let/lambda patterns)
    "anthill.reflect.Pattern.var_pattern",
    "anthill.reflect.Pattern.tuple_pattern",
    "anthill.reflect.Pattern.named_tuple_pattern",
    "anthill.reflect.Pattern.constructor_pattern",
    "anthill.reflect.Pattern.literal_pattern",
    "anthill.reflect.Pattern.wildcard",
    // Literal carriers — `[…]` / `{…}` / `(…)` lower to these (WI-007 / WI-285).
    // `convert_term_with_expected` keys its context-aware desugaring on the
    // resolved qualified name (`anthill.reflect.ListLiteral`), so the carrier
    // MUST resolve here, not bare-intern.
    "anthill.reflect.ListLiteral",
    "anthill.reflect.SetLiteral",
    "anthill.reflect.TupleLiteral",
    // Reflection PRIMITIVES — `field_access` (`x.field`) is emitted for every
    // member access; the rest are reflect-specific introspection helpers.
    "anthill.reflect.field_access",
    "anthill.reflect.as_term",
    "anthill.reflect.SourceSpan.source_span",
    "anthill.reflect.occurrence_owner",
    "anthill.reflect.occurrence_span",
    "anthill.reflect.occurrence_term",
    "anthill.reflect.sub_occurrences",
];

/// WI-040: short name → qualified target for the reserved kernel desugaring vocab,
/// or `None` if `name` is not reserved. Resolved directly (no `_global` import).
fn kernel_vocab_qualified(name: &str) -> Option<&'static str> {
    KERNEL_VOCAB_QUALIFIED
        .iter()
        .copied()
        .find(|qn| qn.rsplit('.').next() == Some(name))
}

/// WI-521: the implicit PRELUDE — user-facing names auto-available in every
/// namespace without an `import` line: the fundamental constructors, the
/// arithmetic / comparison operator targets (`+` → `add`, `=` → `eq`, …, via
/// `parse/pratt.rs`), and the logic operators (`not` / `or`). Like the kernel
/// vocab (WI-040), these resolve via a LOWEST-PRECEDENCE fallback rather than a
/// `_global` import: a user's local definition or explicit import always wins
/// (the fallback fires only when scope resolution fails) and the import can never
/// go AMBIGUOUS against a user name — the failure mode the old flat
/// `add_import(_global, …)` had, which forced the WI-476 collision blocklist.
///
/// `not` → `anthill.reflect.not` keeps the boolean-`!` / negation-as-failure
/// conflation INTACT (a deliberate, separate decision — its own ticket).
/// `push_choice` (the kernel disjunction primitive that `or` lifts) is here too:
/// it is a globally-visible language primitive, named bare from any namespace.
/// The reflection `*Info` result sorts are here as well — a reflection vocabulary
/// queried bare by reflection infrastructure (the `anthill-stl` bridge / CLI);
/// `reflect/typing.anthill` still imports them explicitly (the fallback is below
/// that import in precedence, so the import wins where present).
const PRELUDE_QUALIFIED: &[&str] = &[
    "anthill.prelude.List.cons",
    "anthill.prelude.List.nil",
    "anthill.prelude.Option.some",
    "anthill.prelude.Option.none",
    // WI-644 / proposal 004: the partial comparison ops live on the PartialEq /
    // PartialOrd bases (Eq / Ordered are the lawful/total markers above them). A
    // bare `eq`/`gt`/… resolves to the base op via this fallback.
    "anthill.prelude.PartialEq.eq",
    "anthill.prelude.PartialEq.neq",
    "anthill.prelude.PartialOrd.gt",
    "anthill.prelude.PartialOrd.lt",
    "anthill.prelude.PartialOrd.gte",
    "anthill.prelude.PartialOrd.lte",
    "anthill.prelude.Numeric.add",
    "anthill.prelude.Numeric.sub",
    "anthill.prelude.Numeric.mul",
    "anthill.prelude.Numeric.neg",  // prefix `-` (WI-529); not position-directed
    // WI-529: `&`/word-`and` is value-only (no goal connective — conjunction is the
    // comma, there is no kernel.and), so it resolves to the dispatched Bool op
    // everywhere via this general fallback. `not`/`or` are position-directed instead
    // (resolver primitives by default; Bool.not/Bool.or only inside an operation body,
    // handled in remap_name_str via in_op_body_value).
    "anthill.prelude.Bool.and",
    "anthill.prelude.BigInt.to_bigint",
    "anthill.prelude.BigInt.to_int",
    "anthill.reflect.not",         // logic operator `not` / `!` (NAF; conflation deferred)
    "anthill.kernel.or",           // logic operator `or` / `|`
    "anthill.kernel.push_choice",  // kernel disjunction primitive (`or` lifts it)
    "anthill.kernel.unify",        // structural-unification primitive (`<=>` / `let` lift it)
    "anthill.kernel.struct_eq",    // structural identity test (`===`); proposal 051 / WI-615
    "anthill.kernel.find_dictionary", // rule-body requirement guard (`requires(X)`); WI-300
    "anthill.kernel.cut",          // cut control primitive (`!`); proposal 033.1 / WI-568
    // Reflection result sorts — a reflection VOCABULARY queried bare (by short
    // name) from reflection infrastructure (the `anthill-stl` reflect bridge's
    // `SortQuery`, CLI reflection queries). Globally resolvable like the rest, and
    // — being on the fallback — still shadowable and never ambiguous against a
    // user sort of the same name (e.g. a user `entity SortView`).
    "anthill.reflect.SortInfo",
    "anthill.reflect.FieldInfo",
    "anthill.reflect.OperationInfo",
    "anthill.reflect.EntityInfo",
    "anthill.reflect.SortRequiresInfo",
    "anthill.reflect.SortProvidesInfo",
    "anthill.reflect.SortView",
];

/// WI-521: short name → qualified target for the implicit prelude, or `None`.
/// Resolved as a lowest-precedence fallback (no `_global` import); a user name
/// in scope always shadows it.
fn prelude_qualified(name: &str) -> Option<&'static str> {
    PRELUDE_QUALIFIED
        .iter()
        .copied()
        .find(|qn| qn.rsplit('.').next() == Some(name))
}

/// WI-040 / WI-521: short name → qualified target for ALL implicitly-available
/// names — the reserved kernel desugaring vocab and the implicit prelude — or
/// `None`. The single source every resolver consults as a LOWEST-PRECEDENCE
/// fallback (after scope resolution fails), so a user name in scope always wins.
/// Callers: `remap_name_str` (loader), `resolve_name_in_kb_opt` (query patterns),
/// `KnowledgeBase::resolve_name_in_global` (the reflect bridge).
pub(crate) fn implicit_qualified(name: &str) -> Option<&'static str> {
    kernel_vocab_qualified(name).or_else(|| prelude_qualified(name))
}

/// Check if a scope term represents a sort (vs. the global scope or a namespace).
/// Heuristic: if the scope has a symbol defined as Sort kind, it's a sort scope.
fn is_sort_scope(kb: &KnowledgeBase, scope: TermId) -> bool {
    if let Term::Fn { functor, pos_args, named_args } = kb.get_term(scope) {
        if pos_args.is_empty() && named_args.is_empty() {
            if let crate::intern::SymbolDef::Resolved { kind: SymbolKind::Sort, .. } = kb.symbols.get(*functor) {
                return true;
            }
        }
    }
    false
}

/// For a dotted name like `"a.b.C"`, create implicit intermediate namespaces
/// `"a"` and `"a.b"` (if they don't already exist), returning the short name
/// (`"C"`) and the innermost scope (`a.b`'s term).
///
/// If the name has no dots, returns `(full_name, outer_scope)` unchanged.
///
/// `prefix` is the fully-qualified path of the enclosing scope. Intermediate
/// namespaces get qualified names prepended with this prefix.
fn ensure_intermediate_namespaces(
    kb: &mut KnowledgeBase,
    full_name: &str,
    outer_scope: TermId,
    prefix: &str,
) -> (String, TermId) {
    let segments: Vec<&str> = full_name.split('.').collect();
    if segments.len() <= 1 {
        return (full_name.to_owned(), outer_scope);
    }

    let mut current_scope = outer_scope;
    // Process all segments except the last one — each becomes a namespace
    for i in 0..segments.len() - 1 {
        let path: String = segments[..=i].join(".");
        let qualified_path = make_qualified(prefix, &path);
        let short = segments[i];

        // Check if this namespace already exists in the current scope
        let existing = kb.symbols.by_qualified_name.get(&qualified_path).copied().filter(|&sym| {
            matches!(
                kb.symbols.get(sym),
                SymbolDef::Resolved { kind: SymbolKind::Namespace, scope_raw, .. }
                if *scope_raw == current_scope.raw()
            )
        });

        let ns_term = if let Some(sym) = existing {
            // Reuse existing namespace
            kb.alloc(Term::Fn {
                functor: sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            })
        } else {
            // Create implicit namespace
            let sym = kb.symbols.define(short, &qualified_path, SymbolKind::Namespace, current_scope.raw());
            let ns_term = kb.alloc(Term::Fn {
                functor: sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            // Enclosing scope is visible from within this namespace
            kb.symbols.add_parent(ns_term.raw(), ScopeInclusion {
                parent_scope_raw: current_scope.raw(),
                instantiation_term_raw: current_scope.raw(),
                is_enclosing: true,
            });
            ns_term
        };

        current_scope = ns_term;
    }

    (segments.last().unwrap().to_string(), current_scope)
}

/// WI-499: register an entity's ordered field NAMES into the KB during
/// `scan_definitions` pass-1 — BEFORE any term conversion — so the WI-433
/// positional→named desugar, the partial-named-arg expansion, and the
/// over-arity loud check (all of which gate on `kb.entity_field_names`) are
/// load-order-INDEPENDENT. A positional constructor whose entity is declared
/// textually AFTER the referencing fact/rule (same namespace), or in a
/// later-loaded file, used to see `entity_field_names = None` at convert time
/// and silently stay positional (the WI-433 never-match, just reordered) while
/// the over-arity error was silently skipped — because field names were only
/// registered later, in `load_entity` during the source-order load pass.
///
/// Field NAMES only: the field TYPES (literal-typing hints) need the type-aware
/// `type_expr_to_value` lowering and stay in `load_entity`. Names are registered
/// under both the resolved entity symbol (the `remap_name` / `remap_symbol` key
/// the convert path uses) and the bare-interned short name (the key
/// sugar-generated facts use), mirroring the dual registration the loader did.
///
/// Idempotent (`register_entity_fields` overwrites): a re-scanned or
/// prelude-bootstrapped entity simply re-registers the same names.
fn register_entity_field_names_scan(
    kb: &mut KnowledgeBase,
    parse_sym: &crate::intern::SymbolTable,
    e: &Entity,
    entity_sym: Symbol,
    short: &str,
) {
    let field_names: Vec<Symbol> = e
        .fields
        .iter()
        .map(|f| kb.intern(parse_sym.name(f.name)))
        .collect();
    kb.register_entity_fields(entity_sym, field_names.clone());
    // Sugar-generated facts reference the bare short name (`kb.intern("WorkItem")`,
    // an Unresolved symbol distinct from the resolved entity symbol), so register
    // under it too — unless it coincides with the resolved symbol.
    let short_sym = kb.intern(short);
    if short_sym != entity_sym {
        kb.register_entity_fields(short_sym, field_names);
    }
}

/// Create an operation scope and define its parameters plus the reserved
/// `result` name (proposal 041).
///
/// Operations always get their own scope so that:
/// - Parameter names are resolvable in effects clauses (e.g., `effects
///   (Modify[store])` where `store` is a parameter).
/// - The reserved name `result` is resolvable in effects and ensures
///   positions to refer to the operation's return value (proposal 041).
///   For named-tuple returns, components are accessed via the existing
///   field-projection syntax (`result.a`, per kernel-language.md §6.7).
///
/// Param-name conflict with `result` is checked at load time
/// (`load_operation`), not here — scan only defines symbols.
fn scan_operation_params(
    kb: &mut KnowledgeBase,
    parse_sym: &crate::intern::SymbolTable,
    op: &Operation,
    op_sym: Symbol,
    enclosing_scope: TermId,
    prefix: &str,
) {
    // Allocate the scope term unconditionally so paramless ops still
    // resolve `result`.
    let op_term = kb.make_name_term_from_sym(op_sym);
    kb.symbols.add_parent(op_term.raw(), ScopeInclusion {
        parent_scope_raw: enclosing_scope.raw(),
        instantiation_term_raw: enclosing_scope.raw(),
        is_enclosing: true,
    });

    // Register each op type param as a Sort symbol AND flag it as a
    // type-param so bare uses (`x: T`) route through the type-param
    // branch in `type_expr_to_child` — same mechanism as `sort T = ?`
    // inside a sort body.
    for tp in &op.type_params {
        let tp_name = parse_sym.name(tp.name);
        let qualified = make_qualified(prefix, tp_name);
        kb.symbols.define(tp_name, &qualified, SymbolKind::Sort, op_term.raw());
        kb.symbols.add_type_param(op_term.raw(), tp_name);
    }

    // WI-352: the op's ordered argument-place symbols, recorded on the op
    // symbol so a self-recursive `apply(op, args)` maps `args[i]` to the op's
    // i-th param place from symbol data alone (the flow-derivation pass).
    let mut op_arg_places: Vec<Symbol> = Vec::new();
    for p in &op.params {
        let param_name = parse_sym.name(p.name);
        // Skip param-name `result` here; the load pass reports the
        // collision with the reserved return-value name.
        if param_name == "result" {
            continue;
        }
        let qualified = make_qualified(prefix, param_name);
        // WI-352: an op parameter's `SymbolKind::Param` *is* its place
        // classification (provenance `input`) — no side-table.
        let param_sym =
            kb.symbols.define(param_name, &qualified, SymbolKind::Param, op_term.raw());
        op_arg_places.push(param_sym);

        // WI-352: a callback-typed parameter contributes its own places — a
        // `CallbackParam` per arrow param and a `CallbackResult` for the arrow
        // return, qualified under `<op>.<param>` (`foldLeft.f.a`, `foldLeft.f.t`,
        // `foldLeft.f.result`). These are the projection references the
        // `Modify` feed/flow analysis names (docs/design/modify-effect-derive.md
        // §"Where flow facts live"), generalizing proposal 041's lone
        // `<op>.result`. `register_callback_places` recurses, so a param or
        // result that is *itself* an arrow is descended into and arbitrarily
        // nested callbacks (`f.g.x`, `f.result.z`) all get places.
        if let TypeExpr::Arrow { params, return_type, .. } = &p.ty {
            register_callback_places(
                kb,
                parse_sym,
                params,
                return_type,
                op_term.raw(),
                prefix,
                param_name,
            );
        }
    }
    // WI-352: publish the op's ordered argument places on the op symbol.
    kb.symbols.set_arg_places(op_sym, op_arg_places);

    let result_qualified = make_qualified(prefix, "result");
    // WI-352: the reserved result binder carries its role in its kind —
    // `OpResult` (provenance `op_result`). `is_result_binder` and WI-314 region
    // masking key on this kind; no side-table registration.
    kb.symbols.define("result", &result_qualified, SymbolKind::OpResult, op_term.raw());

    // WI-262: `result.<field>` per-component projection (`Modify[result.a]`) is
    // now lowered uniformly by the type-level projection path — the dotted name's
    // head `result` (an `OpResult` value place) routes through
    // `try_denoted_value_path`, which builds the value-in-type `denoted` place
    // BEFORE the qualified-name `remap_name` fallback. So no synthetic
    // `result.<field>` symbol is needed (this is the same path that serves
    // `Modify[c.field]` for an entity/tuple-typed param). The WI-261 workaround
    // that pre-registered those symbols is removed.
}

/// WI-352: recursively define the places of a callback (arrow) type rooted at
/// `rel_path` — the dotted path from the operation to this callback (`f`, or
/// `f.g` for a nested one), classifying each by its `SymbolKind`. Each arrow
/// param becomes a `CallbackParam` place `<op>.<rel_path>.<name>` and the arrow
/// return a `CallbackResult` place `<op>.<rel_path>.result`; a param or result
/// that is *itself* an arrow is descended into, so arbitrarily nested callbacks
/// (`f.g.x`, `f.result.z`) all resolve to a place. Param names are read off the
/// parse-IR arrow (WI-355 preserves them); unnamed params fall back to the
/// 1-based positional `_{i+1}` matching the arrow-type lowering (spec §4.5). All
/// places share the operation's scope (`op_scope_raw`) and qualified `prefix`.
/// Recursion terminates with the (finite) parse tree — no cycles to bound.
fn register_callback_places(
    kb: &mut KnowledgeBase,
    parse_sym: &crate::intern::SymbolTable,
    params: &[(Option<Symbol>, TypeExpr)],
    return_type: &TypeExpr,
    op_scope_raw: u32,
    prefix: &str,
    rel_path: &str,
) {
    // WI-352: this callback's ordered argument-place symbols, published on the
    // callback's own symbol (so `apply(f, args)` maps positionally from symbol
    // data — the flow-derivation pass).
    let mut cb_arg_places: Vec<Symbol> = Vec::new();
    for (i, (cb_name_sym, cb_ty)) in params.iter().enumerate() {
        let cb_name = match cb_name_sym {
            Some(s) => parse_sym.name(*s).to_owned(),
            // Unnamed arrow param: 1-based positional (`_1`, `_2`, …; spec §4.5).
            None => format!("_{}", i + 1),
        };
        // `result` is reserved for the callback return (registered below); a
        // param so named would collide with it, so skip — mirroring the
        // op-level reservation.
        if cb_name == "result" {
            continue;
        }
        let sub_path = format!("{}.{}", rel_path, cb_name);
        let qualified = make_qualified(prefix, &sub_path);
        let cb_sym =
            kb.symbols.define(&sub_path, &qualified, SymbolKind::CallbackParam, op_scope_raw);
        cb_arg_places.push(cb_sym);
        // A param that is itself a callback — descend.
        if let TypeExpr::Arrow { params: inner, return_type: inner_ret, .. } = cb_ty {
            register_callback_places(
                kb, parse_sym, inner, inner_ret, op_scope_raw, prefix, &sub_path,
            );
        }
    }
    // The callback's own result place — `<op>.<rel_path>.result`.
    let res_path = format!("{}.result", rel_path);
    let qualified = make_qualified(prefix, &res_path);
    kb.symbols.define(&res_path, &qualified, SymbolKind::CallbackResult, op_scope_raw);
    // A result that is itself a callback (a curried op) — descend.
    if let TypeExpr::Arrow { params: inner, return_type: inner_ret, .. } = return_type {
        register_callback_places(
            kb, parse_sym, inner, inner_ret, op_scope_raw, prefix, &res_path,
        );
    }
    // Publish the ordered arg places on this callback's symbol (`<op>.<rel_path>`).
    let self_qn = make_qualified(prefix, rel_path);
    if let Some(self_sym) = kb.symbols.by_qualified_name.get(&self_qn).copied() {
        kb.symbols.set_arg_places(self_sym, cb_arg_places);
    }
}

/// Sub-pass 1: define all names, record exposed variants and type params.
///
/// `prefix` is the fully-qualified path of the enclosing scope (empty at top level).
/// Nested items get `qualified_name = prefix + "." + name`.
/// Define a rule's label as a scoped symbol (pass 1). The head-functor Goal
/// identity is registered later, in `scan_rule_goal` (pass 3), once `requires`
/// parents are wired — see proposal 044.
fn scan_rule(
    kb: &mut KnowledgeBase,
    r: &Rule,
    parse_sym: &crate::intern::SymbolTable,
    scope: TermId,
    prefix: &str,
) {
    if let Some(ref label) = r.label {
        let name = join_segments(parse_sym, &label.segments);
        let qualified = make_qualified(prefix, &name);
        kb.symbols.define(&name, &qualified, SymbolKind::Rule, scope.raw());
    }
}

/// Register an unlabeled rule's head functor as a scoped Goal symbol — UNLESS
/// the name already resolves in scope (proposal 044 / B2). The transitional
/// load strategy (proposal 032) is:
///
///   * labeled rule: the label IS the rule's identity (registered in pass 1);
///     no separate Goal entry is needed.
///   * unlabeled single-head rule: the head functor IS the rule's identity.
///
/// B2: when the head functor already resolves — an operation inherited via
/// `requires` (e.g. `Ordered`'s `eq` law resolving to `PartialEq.eq`), or a locally
/// declared operation — the rule binds to that ORIGIN symbol instead of
/// minting a shadowing sort-local `Goal`. Only a genuinely-new head predicate
/// (NotFound) gets a fresh Goal. Runs in pass 3 so the `requires` parent chain
/// is already wired.
fn scan_rule_goal(
    kb: &mut KnowledgeBase,
    r: &Rule,
    parse_sym: &crate::intern::SymbolTable,
    parse_terms: &SimpleTermStore,
    scope: TermId,
    prefix: &str,
) {
    if r.label.is_some() {
        return;
    }
    if let Some(functor_name) = unlabeled_head_functor_name(r, parse_sym, parse_terms) {
        if matches!(
            kb.symbols.resolve_in_scope(functor_name, scope.raw()),
            crate::intern::ResolveResult::NotFound
        ) {
            // WI-530: don't shadow an equation-connective head. `eq` / `unify`
            // are the `=` / `<=>` desugar (proposal 049) and live in the implicit
            // prelude, so they resolve to the canonical `anthill.prelude.PartialEq.eq` /
            // `anthill.kernel.unify` at load time (`remap_name_str` consults
            // `implicit_qualified`). Minting a `<ns>.eq` / `<ns>.unify` Goal here
            // would instead index a (migrated) equation under that local shadow,
            // silently hiding it from `apply_eq_rules`, whose selection keys on the
            // canonical functor — and would force every `<=>` equation to carry an
            // `import anthill.kernel.{unify}`. The skip is deliberately NARROW (only
            // these two connectives) so a user PREDICATE rule with any other
            // reserved-name head (`or` / `not` / …) still gets its own Goal symbol
            // rather than silently rerouting to the kernel primitive — the
            // regression the broad "skip every implicit name" attempt hit (WI-523
            // handoff). The check is the STATIC `implicit_qualified` const, not the
            // load-order-dependent `by_qualified_name` lookup that made that attempt
            // flaky.
            let is_equation_connective = (functor_name == "eq" || functor_name == "unify")
                && implicit_qualified(functor_name).is_some();
            if !is_equation_connective {
                let qualified = make_qualified(prefix, functor_name);
                kb.symbols.define(functor_name, &qualified, SymbolKind::Goal, scope.raw());
            }
        }
    }
}

/// For an unlabeled rule with a single positive Fn head, return the
/// head's functor name. Multi-head, denial, or non-Fn heads return
/// None.
fn unlabeled_head_functor_name<'a>(
    r: &Rule,
    parse_sym: &'a crate::intern::SymbolTable,
    parse_terms: &SimpleTermStore,
) -> Option<&'a str> {
    if r.heads.len() != 1 {
        return None;
    }
    if let RuleHead::Term(tid) = &r.heads[0] {
        if let Term::Fn { functor, .. } = parse_terms.get(*tid) {
            return Some(parse_sym.name(*functor));
        }
    }
    None
}

/// WI-369: record the parse-IR `internal` visibility flag on a defined symbol,
/// so cross-scope resolution hides it (kernel-language.md §8.6). `public` /
/// unspecified is the visible default and records nothing.
fn record_internal(kb: &mut KnowledgeBase, sym: Symbol, vis: Option<Visibility>) {
    if vis == Some(Visibility::Internal) {
        kb.symbols.mark_internal(sym);
    }
}

fn scan_items_pass1(
    kb: &mut KnowledgeBase,
    items: &[Item],
    parse_sym: &crate::intern::SymbolTable,
    parse_terms: &SimpleTermStore,
    scope: TermId,
    prefix: &str,
) {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                let name = join_segments(parse_sym, &s.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                // Reuse existing sort symbol if already defined (e.g. by register_prelude)
                let (sym, is_new) = if let Some(&existing) = kb.symbols.by_qualified_name.get(&qualified) {
                    (existing, false)
                } else {
                    (kb.symbols.define(&short, &qualified, SymbolKind::Sort, actual_scope.raw()), true)
                };
                record_internal(kb, sym, s.visibility);
                let sort_term = kb.alloc(Term::Fn {
                    functor: sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::new(),
                });
                if is_new {
                    // Implicit parent: the enclosing scope is visible from within the sort
                    kb.symbols.add_parent(sort_term.raw(), ScopeInclusion {
                        parent_scope_raw: actual_scope.raw(),
                        instantiation_term_raw: actual_scope.raw(),
                        is_enclosing: true,
                    });
                }
                // Model C / job 2 (proposal 044): names are visible by default;
                // the `export` statement was removed (WI-291). The `exposed` set
                // now holds ONLY entity-variant names (populated below), so the
                // exposed-set filter on the variant-exposure parent link leaks
                // just the constructor variants, never the sort's operations.
                //
                // Expose the sort's constructor variants to the enclosing
                // scope: add each `entity` child short-name to the sort's
                // `exposed` set and link the sort scope as a non-enclosing
                // parent of `actual_scope`. The exposed-filtered parent walk in
                // `resolve_in_scope` then resolves bare `Open` to
                // `WorkStatus.Open` from the namespace, and two sorts sharing a
                // variant name resolve to `Ambiguous` rather than one winning.
                //
                // The parent link is added only when the sort has variants: an
                // empty `exposed` set disables the filter (a no-entity sort, e.g.
                // a spec, is reachable only via `requires`/wildcard, which should
                // see all its operations).
                let mut has_variant = false;
                for item in &s.items {
                    if let Item::Entity(e) = item {
                        let vshort = parse_sym.name(*e.name.segments.last().unwrap());
                        kb.symbols.add_exposed(sort_term.raw(), vshort);
                        has_variant = true;
                    }
                }
                if is_new && has_variant {
                    kb.symbols.add_parent(actual_scope.raw(), ScopeInclusion {
                        parent_scope_raw: sort_term.raw(),
                        instantiation_term_raw: sort_term.raw(),
                        is_enclosing: false,
                    });
                }
                // WI-452 (§5.4): a MARKED structured param (`sort [F] { … }`, the
                // higher-kinded carrier of `sort Spec[F[T]]`) is a NON-RIGID type
                // parameter of the enclosing sort — register it like the
                // `sort T = ?` arm below does (the `add_type_param` half; the
                // SortAlias → Var backing var is emitted in `load_sort_with_body`).
                // An UNMARKED `sort F { … }` stays a concrete nested sort.
                if s.is_type_param && is_sort_scope(kb, scope) {
                    kb.symbols.add_type_param(scope.raw(), &short);
                }
                // Recurse into sort body with the sort's qualified name as prefix
                scan_items_pass1(kb, &s.items, parse_sym, parse_terms, sort_term, &qualified);
            }
            Item::AbstractSort(s) => {
                let name = join_segments(parse_sym, &s.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                let abstract_sym = kb.symbols.define(&short, &qualified, SymbolKind::Sort, actual_scope.raw());
                record_internal(kb, abstract_sym, s.visibility);
                // `sort T = ?` inside a SortWithBody or EnumDecl = type parameter
                if matches!(s.definition, TypeExpr::Variable { .. }) && is_sort_scope(kb, scope) {
                    kb.symbols.add_type_param(scope.raw(), &short);
                }
            }
            Item::Namespace(n) => {
                let name = join_segments(parse_sym, &n.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                // Reuse existing namespace symbol if already defined in the same scope
                // (multiple files can contribute items to the same namespace).
                let existing = kb.symbols.by_qualified_name.get(&qualified).copied().filter(|&sym| {
                    matches!(
                        kb.symbols.get(sym),
                        SymbolDef::Resolved { kind: SymbolKind::Namespace, scope_raw, .. }
                        if *scope_raw == actual_scope.raw()
                    )
                });
                let (_sym, ns_term) = if let Some(sym) = existing {
                    let ns_term = kb.alloc(Term::Fn {
                        functor: sym,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::new(),
                    });
                    (sym, ns_term)
                } else {
                    let sym = kb.symbols.define(&short, &qualified, SymbolKind::Namespace, actual_scope.raw());
                    let ns_term = kb.alloc(Term::Fn {
                        functor: sym,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::new(),
                    });
                    // Implicit parent: the enclosing scope is visible from within the namespace
                    kb.symbols.add_parent(ns_term.raw(), ScopeInclusion {
                        parent_scope_raw: actual_scope.raw(),
                        instantiation_term_raw: actual_scope.raw(),
                        is_enclosing: true,
                    });
                    (sym, ns_term)
                };
                // Model C / job 2 (proposal 044): namespace members are visible
                // by default; the `export` statement was removed (WI-291).
                // Recurse into namespace body with the namespace's qualified name as prefix
                scan_items_pass1(kb, &n.items, parse_sym, parse_terms, ns_term, &qualified);
            }
            Item::Entity(e) => {
                let name = join_segments(parse_sym, &e.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                // Reuse existing entity symbol if already defined (e.g. by register_prelude)
                let entity_sym = if let Some(&existing) = kb.symbols.by_qualified_name.get(&qualified) {
                    existing
                } else {
                    kb.symbols.define(&short, &qualified, SymbolKind::Entity, actual_scope.raw())
                };
                record_internal(kb, entity_sym, e.visibility);
                // WI-499: register field NAMES now, before any term conversion, so the
                // positional→named desugar / partial-expansion / over-arity check are
                // load-order-independent. Field TYPES stay in load_entity.
                register_entity_field_names_scan(kb, parse_sym, e, entity_sym, &short);
            }
            Item::Operation(o) => {
                let name = join_segments(parse_sym, &o.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                let op_sym = kb.symbols.define(&short, &qualified, SymbolKind::Operation, actual_scope.raw());
                record_internal(kb, op_sym, o.visibility);
                scan_operation_params(kb, parse_sym, o, op_sym, actual_scope, &qualified);
            }
            Item::Const(c) => {
                // Proposal 039 / WI-084: define the constant's symbol (pass 1, like
                // operations). Monomorphic + carrier-independent — no params or
                // type-params to scan. The declared type + body are recorded in
                // the load phase (`load_const`).
                let name = join_segments(parse_sym, &c.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                let const_sym = kb.symbols.define(&short, &qualified, SymbolKind::Const, actual_scope.raw());
                record_internal(kb, const_sym, c.visibility);
            }
            Item::OperationBlock(ob) => {
                for op in &ob.entries {
                    let name = join_segments(parse_sym, &op.name.segments);
                    let qualified = make_qualified(prefix, &name);
                    let op_sym = kb.symbols.define(&name, &qualified, SymbolKind::Operation, scope.raw());
                    record_internal(kb, op_sym, op.visibility);
                    scan_operation_params(kb, parse_sym, op, op_sym, scope, &qualified);
                }
            }
            Item::Rule(r) => {
                scan_rule(kb, r, parse_sym, scope, prefix);
            }
            Item::RuleBlock(rb) => {
                for rule in &rb.entries {
                    scan_rule(kb, rule, parse_sym, scope, prefix);
                }
            }
            Item::Constraint(_) => {
                // Constraints don't define named symbols
            }
            // Stage 0 items, facts, requires — handled elsewhere or not names
            _ => {}
        }
    }
}

/// Sub-pass 2: process requires declarations and imports → build parent scope chain.
///
/// `prefix` is the fully-qualified path of the enclosing scope (empty at top level).
fn scan_items_pass2(
    kb: &mut KnowledgeBase,
    items: &[Item],
    parse_sym: &crate::intern::SymbolTable,
    scope: TermId,
    prefix: &str,
    errors: &mut Vec<LoadError>,
    pending: &mut Vec<PendingImport>,
) {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                let name = join_segments(parse_sym, &s.name.segments);
                let qualified = make_qualified(prefix, &name);
                if let Some(sort_term) = find_scope_by_name(kb, &qualified) {
                    process_imports(kb, parse_sym, &s.imports, sort_term, errors, pending);
                    scan_items_pass2(kb, &s.items, parse_sym, sort_term, &qualified, errors, pending);
                }
            }
            Item::Namespace(n) => {
                let name = join_segments(parse_sym, &n.name.segments);
                let qualified = make_qualified(prefix, &name);
                if let Some(ns_term) = find_scope_by_name(kb, &qualified) {
                    // Process namespace-level imports
                    process_imports(kb, parse_sym, &n.imports, ns_term, errors, pending);
                    // Recurse
                    scan_items_pass2(kb, &n.items, parse_sym, ns_term, &qualified, errors, pending);
                }
            }
            Item::RequiresDecl(r) => {
                let req_sort_name = type_expr_base_name(parse_sym, &r.type_expr);
                // The `effects E = ?` desugar's `requires anthill.prelude.EffectsRuntime[…]`
                // anchor is a synthetic effect-runtime kind-marker, NOT a spec whose scope a
                // sort should resolve names against. Wiring it as a scope parent would splice
                // the ENTIRE prelude namespace in as a resolution parent of every effects-
                // bearing sort, resurfacing prelude sorts as phantom rivals of user sorts that
                // share their short name — the WI-422 ambiguous-symbol class (`sort Option`
                // referenced inside an `effects E = ?` sort would collide with
                // `anthill.prelude.Option`). Before WI-703 the bare anchor name usually failed
                // to resolve here, so no parent was wired by accident; now that it resolves by
                // canonical name the skip must be explicit — matching every other subsystem's
                // EffectsRuntime exemption (WI-703).
                if req_sort_name != "anthill.prelude.EffectsRuntime" {
                    // Use scope-aware resolution first (handles imported/aliased names),
                    // falling back to qualified-name lookup.
                    let req_scope = resolve_name_to_scope(kb, &req_sort_name, scope)
                        .or_else(|| find_scope_by_name(kb, &req_sort_name));
                    if let Some(req_scope) = req_scope {
                        // Create instantiation term
                        let inst_term = build_instantiation_term(kb, parse_sym, &r.type_expr, scope);
                        kb.symbols.add_parent(scope.raw(), ScopeInclusion {
                            parent_scope_raw: req_scope.raw(),
                            instantiation_term_raw: inst_term.raw(),
                            is_enclosing: false,
                        });
                    }
                }
            }
            _ => {}
        }
    }
}

/// Sub-pass 3: register unlabeled rule head functors as Goal symbols, now that
/// `requires`/import parents are wired (pass 2). A head functor that already
/// resolves — an inherited operation or a locally declared one — binds to that
/// origin rather than minting a shadowing sort-local symbol (proposal 044 / B2).
fn scan_items_pass3(
    kb: &mut KnowledgeBase,
    items: &[Item],
    parse_sym: &crate::intern::SymbolTable,
    parse_terms: &SimpleTermStore,
    scope: TermId,
    prefix: &str,
) {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                let name = join_segments(parse_sym, &s.name.segments);
                let qualified = make_qualified(prefix, &name);
                if let Some(sort_term) = find_scope_by_name(kb, &qualified) {
                    scan_items_pass3(kb, &s.items, parse_sym, parse_terms, sort_term, &qualified);
                }
            }
            Item::Namespace(n) => {
                let name = join_segments(parse_sym, &n.name.segments);
                let qualified = make_qualified(prefix, &name);
                if let Some(ns_term) = find_scope_by_name(kb, &qualified) {
                    scan_items_pass3(kb, &n.items, parse_sym, parse_terms, ns_term, &qualified);
                }
            }
            Item::Rule(r) => scan_rule_goal(kb, r, parse_sym, parse_terms, scope, prefix),
            Item::RuleBlock(rb) => {
                for rule in &rb.entries {
                    scan_rule_goal(kb, rule, parse_sym, parse_terms, scope, prefix);
                }
            }
            _ => {}
        }
    }
}

/// Get the base name of a TypeExpr (ignoring bindings).
fn type_expr_base_name(parse_sym: &crate::intern::SymbolTable, ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Simple(name) => join_segments(parse_sym, &name.segments),
        TypeExpr::Parameterized { name, .. } => join_segments(parse_sym, &name.segments),
        TypeExpr::Variable { .. } => "?".to_owned(),
        TypeExpr::Tuple(_) => "TupleLiteral".to_owned(),
        TypeExpr::Arrow { effects, .. } if !effects.is_empty() => "arrow_effect".to_owned(),
        TypeExpr::Arrow { .. } => "arrow".to_owned(),
        TypeExpr::Denoted(_) => "denoted".to_owned(),
        // WI-327: nested base name peeks past the absence wrapper.
        TypeExpr::EffectAbsent(inner) => type_expr_base_name(parse_sym, inner),
        // WI-375: a written effect-row's base is the `effects_rows` bridge entity.
        TypeExpr::EffectRow(_) => "TypeExtractor.EffectsRows".to_owned(),
        // WI-478: a guarded effect's base is its guarded label (peek past the guard).
        TypeExpr::EffectGuarded { label, .. } => type_expr_base_name(parse_sym, label),
    }
}

/// Resolve a name in the given scope context, returning a scope TermId.
/// Uses the full scope-aware resolution chain (locals, imports, parents).
fn resolve_name_to_scope(kb: &mut KnowledgeBase, name: &str, scope: TermId) -> Option<TermId> {
    match kb.symbols.resolve_in_scope(name, scope.raw()) {
        crate::intern::ResolveResult::Found(sym) => {
            Some(kb.alloc(Term::Fn {
                functor: sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            }))
        }
        _ => None,
    }
}

/// Find a scope TermId by looking up a qualified name in the symbol table,
/// then reconstructing the nullary Fn term.
fn find_scope_by_name(kb: &mut KnowledgeBase, qualified: &str) -> Option<TermId> {
    let sym = *kb.symbols.by_qualified_name.get(qualified)?;
    Some(kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    }))
}

/// Walk one level of nested scopes under `base_path` looking for a symbol
/// whose short name is `short`. Returns the symbol when exactly one match
/// is found (multiple matches → ambiguous, no match → none).
///
/// Used by selective-import resolution to find enum entities, which live
/// inside the enum's sort scope rather than directly under the surrounding
/// namespace. For example, `parse_ok` in
///   namespace ns
///     enum E { entity parse_ok(...) }
///   end
/// has qualified name `ns.E.parse_ok`, not `ns.parse_ok`. An import
/// `ns.{parse_ok}` should still bind it.
fn find_in_nested_scope(
    kb: &KnowledgeBase,
    base_path: &str,
    short: &str,
) -> Option<crate::intern::Symbol> {
    let needle_suffix = format!(".{short}");
    let prefix = format!("{base_path}.");
    let mut matches: SmallVec<[crate::intern::Symbol; 2]> = SmallVec::new();
    for (qname, sym) in kb.symbols.by_qualified_name.iter() {
        if !qname.starts_with(&prefix) || !qname.ends_with(&needle_suffix) {
            continue;
        }
        // Require exactly one intermediate segment between base and short:
        // base.<intermediate>.short. Keeps the search to immediate children
        // of the base scope (enums and named sub-scopes), not deeper trees.
        let middle = &qname[prefix.len()..qname.len() - needle_suffix.len()];
        if middle.is_empty() || middle.contains('.') {
            continue;
        }
        matches.push(*sym);
    }
    matches.sort_by_key(|s| s.index());
    matches.dedup();
    if matches.len() == 1 { Some(matches[0]) } else { None }
}

/// Build an instantiation term for `requires Eq[T]`.
fn build_instantiation_term(
    kb: &mut KnowledgeBase,
    parse_sym: &crate::intern::SymbolTable,
    type_expr: &TypeExpr,
    current_scope: TermId,
) -> TermId {
    match type_expr {
        TypeExpr::Simple(name) => {
            let n = join_segments(parse_sym, &name.segments);
            // WI-359: a bare name that resolves to an enclosing type-param (the
            // `F` in `requires Ring[F]`, the `T` in `requires Eq[T]`) becomes a
            // `Ref` to that param symbol — so the cross-param binding survives
            // into the requires SortView and `resolve_requires_bindings` can tie
            // it to a concrete value (a generic name term cannot be). Only
            // type-params take this path; concrete sort names keep the
            // scope-lookup so their shape is unchanged.
            if let crate::intern::ResolveResult::Found(sym) =
                kb.symbols.resolve_in_scope(&n, current_scope.raw())
            {
                if super::typing::is_sort_param_symbol(kb, sym) {
                    return kb.alloc(Term::Ref(sym));
                }
            }
            find_scope_by_name(kb, &n)
                .unwrap_or_else(|| kb.make_name_term(&n))
        }
        TypeExpr::Parameterized { name, bindings } => {
            let sort_name = join_segments(parse_sym, &name.segments);
            let sort_sym = kb.symbols.by_qualified_name.get(&sort_name).copied()
                .unwrap_or_else(|| kb.symbols.intern(&sort_name));
            let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
            let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            for b in bindings {
                let val = build_instantiation_term(kb, parse_sym, &b.bound, current_scope);
                match &b.param {
                    Some(p) => {
                        let key = kb.symbols.intern(&join_segments(parse_sym, &p.segments));
                        named_args.push((key, val));
                    }
                    None => {
                        pos_args.push(val);
                    }
                }
            }
            kb.alloc(Term::Fn {
                functor: sort_sym,
                pos_args,
                named_args,
            })
        }
        TypeExpr::Variable { .. } => {
            // Variable in type position → just use a placeholder name term
            kb.make_name_term("?")
        }
        // WI-302/WI-366: a value-in-type binding in this free-fn path. The result
        // feeds only `ScopeInclusion.instantiation_term_raw`, which is vestigial
        // (written but never read) and carries no value-in-types — so a denoted
        // binding lowers to the same `?` placeholder as a bare `?` variable above
        // (no `make_denoted`). The faithful value rides on the SortRequiresInfo /
        // SortProvidesInfo value fact built by `sort_inst_to_value`.
        TypeExpr::Denoted(_) => kb.make_name_term("?"),
        TypeExpr::Tuple(fields) => {
            let tuple_sym = kb.symbols.by_qualified_name.get("anthill.reflect.TupleLiteral").copied()
                .unwrap_or_else(|| kb.symbols.intern("TupleLiteral"));
            let named_args: SmallVec<[(Symbol, TermId); 2]> = fields.iter().map(|(sym, ty)| {
                let key = kb.symbols.intern(parse_sym.name(*sym));
                let val = build_instantiation_term(kb, parse_sym, ty, current_scope);
                (key, val)
            }).collect();
            kb.alloc(Term::Fn {
                functor: tuple_sym,
                pos_args: SmallVec::new(),
                named_args,
            })
        }
        TypeExpr::Arrow { params, return_type, effects } => {
            let functor = if !effects.is_empty() {
                kb.symbols.intern("arrow_effect")
            } else {
                kb.symbols.intern("arrow")
            };
            let mut pos_args: SmallVec<[TermId; 4]> = params.iter()
                .map(|(_, p)| build_instantiation_term(kb, parse_sym, p, current_scope))
                .collect();
            let ret = build_instantiation_term(kb, parse_sym, return_type, current_scope);
            pos_args.push(ret);
            for eff in effects {
                let eff_term = build_instantiation_term(kb, parse_sym, eff, current_scope);
                pos_args.push(eff_term);
            }
            kb.alloc(Term::Fn {
                functor,
                pos_args,
                named_args: SmallVec::new(),
            })
        }
        // WI-327: instantiation-term position for `-E` is not yet used
        // by any caller (absence forms only appear in effects positions,
        // which take the separate make_arrow_type path). Build a
        // placeholder so the match is total; if a caller ever lands a
        // `-E` here it'll surface as a malformed-name binding rather
        // than a panic.
        TypeExpr::EffectAbsent(_) => kb.make_name_term("?absent"),
        // WI-478: guarded effects appear only in effects positions (lowered via
        // `type_expr_to_child`), never in this instantiation-term free-fn path.
        // Placeholder so the match stays total (mirrors `EffectAbsent`).
        TypeExpr::EffectGuarded { .. } => kb.make_name_term("?guarded"),
        // WI-375: a WRITTEN effect-row in this ground free-fn lowering path
        // (`Stream[E = {}]` instantiation). Lower each element to a ground term
        // and assemble the canonical `effects_rows(EffectExpression)` Type — the
        // same builder the typer/loader use elsewhere. A value-in-type label
        // (`Modify[c]`) degrades to its ground form here (this path predates
        // occurrences; see the `Denoted` arm above), which is acceptable for the
        // instantiation-term slot (`instantiation_term_raw`, written-never-read);
        // the faithful occurrence form rides via `type_expr_to_child`.
        TypeExpr::EffectRow(effects) => {
            let effect_ts: Vec<TermId> = effects
                .iter()
                .map(|e| build_instantiation_term(kb, parse_sym, e, current_scope))
                .collect();
            kb.build_canonical_effects_rows(&effect_ts)
        }
    }
}

/// WI-295: a `Selective` import name that didn't resolve in sub-pass 2. A
/// rule-defined predicate's head-functor symbol isn't registered until
/// sub-pass 3 (`scan_rule_goal`), so cross-namespace predicate imports are
/// deferred and re-resolved by `scan_definitions`'s post-pass-3 retry.
struct PendingImport {
    scope_raw: u32,
    short: String,
    qualified: String,
    span: Span,
}

/// WI-369: reject importing an `internal` name into a scope that cannot see it.
/// The `by_qualified_name` / nested-scope import-resolution paths bypass
/// `resolve_in_scope`'s `internal` filter, so the visibility gate is applied
/// here explicitly. Returns `true` (recording a `ForbiddenInternalAccess`) when
/// the import is forbidden, so the caller skips the `add_import`.
fn forbid_internal_import(
    kb: &KnowledgeBase,
    sym: Symbol,
    short: &str,
    scope: TermId,
    span: Span,
    errors: &mut Vec<LoadError>,
) -> bool {
    if kb.symbols.internal_visible_from(sym, scope.raw()) {
        return false;
    }
    let declared_in = match kb.symbols.get(sym) {
        SymbolDef::Resolved { qualified_name, .. } => qualified_name
            .rsplit_once('.')
            .map(|(p, _)| p.to_owned())
            .unwrap_or_else(|| qualified_name.clone()),
        SymbolDef::Unresolved { name } => name.clone(),
    };
    let scope_name = match kb.get_term(scope) {
        Term::Fn { functor, .. } => match kb.symbols.get(*functor) {
            SymbolDef::Resolved { short_name, .. } => short_name.clone(),
            SymbolDef::Unresolved { name } => name.clone(),
        },
        _ => "_unknown".to_owned(),
    };
    errors.push(LoadError::ForbiddenInternalAccess {
        name: short.to_owned(),
        declared_in,
        scope_name,
        span,
    });
    true
}

/// Process `import` declarations → register imported names and parent scopes.
/// Unresolvable import paths produce errors (deferred predicate imports go to
/// `pending` for the post-pass-3 retry — see `PendingImport`).
fn process_imports(
    kb: &mut KnowledgeBase,
    parse_sym: &crate::intern::SymbolTable,
    imports: &[Import],
    scope: TermId,
    errors: &mut Vec<LoadError>,
    pending: &mut Vec<PendingImport>,
) {
    for imp in imports {
        let raw_path = join_segments(parse_sym, &imp.path.segments);
        // Implicit-prelude fallback: a single-segment path like `Modify` that
        // doesn't resolve at top level falls back to `anthill.prelude.<path>`.
        // Mirrors the global short-name visibility of post-WI-215 prelude
        // effect sorts (Modify, Error, Suspension, Branch, MatchFailed).
        let path = if !raw_path.contains('.')
            && kb.symbols.by_qualified_name.get(&raw_path).is_none()
            && find_scope_by_name(kb, &raw_path).is_none()
        {
            let candidate = format!("anthill.prelude.{raw_path}");
            if kb.symbols.by_qualified_name.contains_key(&candidate)
                || find_scope_by_name(kb, &candidate).is_some()
            {
                candidate
            } else {
                raw_path
            }
        } else {
            raw_path
        };
        match &imp.kind {
            ImportKind::Plain => {
                // `import anthill.prelude.List` → make "List" resolvable locally
                // and add the target scope as a parent for accessing its contents.
                let found = kb.symbols.by_qualified_name.get(&path).copied();
                if let Some(original_sym) = found {
                    let short = last_segment(&path);
                    // WI-369: a plain import of an `internal` name across scopes
                    // is a forbidden reference.
                    if !forbid_internal_import(kb, original_sym, short, scope, imp.path.span, errors) {
                        kb.symbols.add_import(scope.raw(), short, original_sym);
                    }
                }
                if let Some(target_scope) = find_scope_by_name(kb, &path) {
                    kb.symbols.add_parent(scope.raw(), ScopeInclusion {
                        parent_scope_raw: target_scope.raw(),
                        instantiation_term_raw: target_scope.raw(),
                        is_enclosing: false,
                    });
                } else if found.is_none() {
                    errors.push(LoadError::UnresolvedImport {
                        path: path.clone(),
                        span: imp.path.span,
                    });
                }
            }
            ImportKind::Selective(names) => {
                // `import anthill.prelude.{Eq, Ordered}` → for each name,
                // register a local alias. Parent-scope links are NOT added here —
                // if sort contents (operations) are needed, use `requires` or
                // wildcard import (`import path.*`) instead.
                //
                // Resolution strategies, in order:
                // 1. Direct qualified-name lookup (e.g., "anthill.prelude.Eq" as a
                //    top-level dotted name).
                // 2. Resolve short name within the base-path scope (catches names
                //    defined directly under the namespace).
                // 3. Walk one level of child sort/enum scopes within the base
                //    namespace. Without this, importing an enum entity by short
                //    name (`import anthill.cli.parse.{parse_ok}` where `parse_ok`
                //    is an entity inside `enum ParseResult`) fails, since its
                //    qualified name is `anthill.cli.parse.ParseResult.parse_ok`
                //    rather than `anthill.cli.parse.parse_ok`.
                let base_scope = find_scope_by_name(kb, &path);
                if base_scope.is_none() && !kb.symbols.by_qualified_name.contains_key(&path) {
                    // The base path itself doesn't resolve
                    errors.push(LoadError::UnresolvedImport {
                        path: path.clone(),
                        span: imp.path.span,
                    });
                }
                for name in names {
                    let short = join_segments(parse_sym, &name.segments);
                    let qualified = format!("{}.{}", path, short);
                    let original_sym = kb.symbols.by_qualified_name.get(&qualified).copied()
                        .or_else(|| {
                            base_scope.and_then(|bs| {
                                match kb.symbols.resolve_in_scope(&short, bs.raw()) {
                                    crate::intern::ResolveResult::Found(sym) => Some(sym),
                                    _ => None,
                                }
                            })
                        })
                        .or_else(|| find_in_nested_scope(kb, &path, &short));
                    if let Some(sym) = original_sym {
                        // WI-369: a selective import of an `internal` name into a
                        // scope that can't see it is a forbidden reference.
                        if !forbid_internal_import(kb, sym, &short, scope, name.span, errors) {
                            kb.symbols.add_import(scope.raw(), &short, sym);
                        }
                    } else {
                        // WI-295: a rule-defined predicate's head-functor symbol
                        // isn't registered until sub-pass 3 (scan_rule_goal),
                        // which runs after imports — so don't error yet. Defer
                        // to scan_definitions's post-pass-3 retry, which
                        // re-resolves it (erroring only if still unbound).
                        pending.push(PendingImport {
                            scope_raw: scope.raw(),
                            short,
                            qualified,
                            span: name.span,
                        });
                    }
                }
            }
            ImportKind::Wildcard => {
                if let Some(target_scope) = find_scope_by_name(kb, &path) {
                    kb.symbols.add_parent(scope.raw(), ScopeInclusion {
                        parent_scope_raw: target_scope.raw(),
                        instantiation_term_raw: target_scope.raw(),
                        is_enclosing: false,
                    });
                } else {
                    errors.push(LoadError::UnresolvedImport {
                        path: path.clone(),
                        span: imp.path.span,
                    });
                }
            }
        }
    }
}

// ── Prelude: built-in primitive sorts ────────────────────────────

/// Primitive sort names that are always available in the global scope.
/// These correspond to the stdlib primitive types (Int64, Float, String, Bool).
pub const PRELUDE_SORTS: &[&str] = &["Int64", "BigInt", "Float", "String", "Bool"];

/// Effect sorts declared inside `namespace anthill.prelude` in
/// stdlib/anthill/prelude/effects.anthill that user code references by
/// short name (e.g. `effects {Modify[s], Error}`). Adding them to the
/// global scope's import list reproduces the implicit-prelude behaviour
/// that file-top-level bare `sort X` declarations had before WI-215.
pub const IMPLICIT_PRELUDE_EFFECTS: &[&str] =
    &["Modify", "Error", "Suspension", "Branch", "MatchFailed", "DivisionByZero"];

/// Wire the implicit-prelude effect sorts (Modify, Error, …) into the
/// global scope's imports. Called after `scan_definitions` so the
/// qualified symbols already exist. Idempotent: re-adding an existing
/// import is harmless.
pub fn register_implicit_prelude_effects(kb: &mut KnowledgeBase) {
    let global_raw = kb.make_name_term("_global").raw();
    for &short in IMPLICIT_PRELUDE_EFFECTS {
        let qualified = format!("anthill.prelude.{short}");
        if let Some(&sym) = kb.symbols.by_qualified_name.get(&qualified) {
            kb.symbols.add_import(global_raw, short, sym);
        }
    }
}

/// KB-internal meta-sort names. Used as sort-of-sort markers (e.g. the sort
/// of a Fact entry is `Fact`). Not defined in any `.anthill` file.
///
/// Registered *qualified-only* (see [`SymbolTable::define_qualified_only`] and
/// the `KERNEL_FUNCTORS` note below): the loader emits the reflection facts that
/// carry these sorts via `make_name_term("Member")` etc., which INTERNS the name
/// (a separate intern-map symbol), never scope-resolves it — so keeping them out
/// of every scope's `locals` is transparent to fact emission. Previously they
/// were bare global *locals* via `define()`, which let a `requires`-induced scope
/// link (sort -> spec -> prelude -> _global) bypass a user's enclosing-chain
/// alias and resurface the kernel meta-sort as a phantom rival to a user sort of
/// the same name (e.g. `sort Member` / `sort Constraint`) referenced bare inside
/// a `requires`-bearing sort -> `ambiguous symbol` (WI-423, the structural twin
/// of the WI-422 functor leak). No `.anthill` source or Rust resolver references
/// these names by scope, so delocalizing closes the leak with no capability loss.
const KERNEL_META_SORTS: &[&str] = &[
    "Sort", "Entity", "Fact", "Rule", "Operation", "Namespace",
    "Requirement", "Description", "Constraint", "Member",
];

/// KB-internal fact functors the loader emits into the KB (never declared in
/// any `.anthill` file). Each is `(short_name, qualified_name)`.
/// (EntityInfo and SortRequiresInfo are now declared in reflect.anthill.)
///
/// Registered *qualified-only* (see [`SymbolTable::define_qualified_only`]): the
/// loader addresses them by qualified name via `resolve_symbol`, but they are
/// kept out of every scope's `locals`, so user name resolution can never
/// surface them. Previously they were bare global *locals*, which let a
/// `requires`-induced scope link resurface the kernel `member` as a phantom
/// rival to a user's `import …List.{member}` alias inside a requires-bearing
/// sort (WI-422). `member` carries the fully-qualified reflect name it deserves
/// as a reflection fact; `meta` / `SortAlias` keep their existing qualified
/// keys (delocalizing alone closes the same latent leak — their many call sites
/// resolve those keys unchanged).
const KERNEL_FUNCTORS: &[(&str, &str)] = &[
    ("SortAlias", "SortAlias"),
    ("member", "anthill.reflect.member"),
    ("meta", "meta"),
];

/// Register primitive sorts and kernel vocabulary in the global scope,
/// plus stdlib scope hierarchy for loader-referenced names.
///
/// Call this before `scan_definitions` / `load` to ensure that references to
/// `Int64`, `Float`, `String`, `Bool` never produce unresolved-name errors,
/// and that all loader-internal functor names are resolvable.
///
/// Stdlib names (`cons`, `nil`, `some`, `none`, `SortInfo`, `FieldInfo`,
/// `OperationInfo`) are defined in their correct scopes with proper
/// qualified names, matching what `scan_definitions` would produce from
/// the stdlib `.anthill` files.  `scan_definitions` is idempotent for these
/// entries and will reuse the existing symbols.
pub fn register_prelude(kb: &mut KnowledgeBase) {
    let global = kb.make_name_term("_global");
    let global_raw = global.raw();
    for &name in KERNEL_META_SORTS {
        kb.symbols
            .define_qualified_only(name, name, SymbolKind::Sort, global_raw);
    }
    for &(short, qualified) in KERNEL_FUNCTORS {
        kb.symbols
            .define_qualified_only(short, qualified, SymbolKind::Entity, global_raw);
    }
    // Stdlib scope hierarchy: create scopes with correct qualified names
    // so the loader's resolve_symbol() finds names in the right scopes.
    // Idempotent: skipped on re-entry or when stdlib has already been scanned.
    register_stdlib_scopes(kb, global_raw);
    // Register builtin operations (eq, gt, add, etc.) for the resolver.
    kb.register_standard_builtins();
    // WI-348: the Type-occurrence field keys (`Denoted.value`, `Arrow.param/
    // result/effects`, `EffectsRows.effects_expr`, `NamedTuple.fields`) are read
    // by the carrier-agnostic `TermView` walk (`goal_fingerprint`, `match_view`,
    // `views_structurally_equal`) via `lookup_symbol`. Intern them so the walk
    // never silently drops a Type occurrence's named child when its key symbol
    // isn't yet registered — keeping `type_node_keys` consistent with the
    // `named_arity` `type_node_head` reports. A full load interns these via the
    // reflect entity defs; this makes lighter `register_prelude` setups agree.
    for &k in &["value", "param", "result", "effects", "effects_expr", "fields"] {
        kb.intern(k);
    }
    // WI-320 (proposal 045 §2.0.1) — emit the EffectsRuntime ↔ effects_rows
    // bridge fact. Lives here in Rust (not in stdlib/effects-runtime.anthill)
    // because surface `_type` doesn't admit entity-construction terms like
    // `effects_rows(?)` in type-arg position — that position is an
    // `application` (the `parameterized_type`/`instantiation_term` rules
    // were merged into one `application` rule under WI-311), and
    // `application` carries a type-arg list, not a value-position
    // entity-construction expression. The fact registers any
    // `effects_rows(...)`-shape Type as a valid `EffectsRuntime[Effects]`
    // binding — the kind discrimination for the `effects E = ? requires
    // EffectsRuntime[E]` desugaring.
    emit_effects_runtime_bridge_fact(kb);
}

/// Emit the WI-320 bridge fact:
/// `EffectsRuntime[Effects = effects_rows(effects_expr = ?fresh)]`.
///
/// Shape-analogous to `fact Effect[T = Modify[?]]` in effects.anthill — both
/// register a parameterized-sort-instantiation pattern as a satisfiable
/// goal — but emitted in Rust because the surface grammar's `_type` rule
/// does not admit entity-construction terms like `effects_rows(?)` in
/// type-arg position. The bridge is also *indexed differently* from the
/// stdlib precedent: a surface-syntax `fact F[…]` without a sort
/// annotation lands in `by_sort[Fact]` and `by_domain[<enclosing-scope>]`
/// (load_fact at load.rs ~5728, `f.sort.unwrap_or("Fact")`), whereas this
/// Rust-emitted fact uses `sort = domain = EffectsRuntime` to keep its
/// intent (a statement about EffectsRuntime) attached to its `by_sort` /
/// `by_domain` keys. Resolution still works through the discrim tree;
/// reflection consumers that enumerate `by_sort["Fact"]` won't see this
/// fact, which is intentional (it isn't a user-written fact). See
/// proposal 045 §2.0.1.
///
/// **Idempotency** — `register_prelude` is called more than once on the
/// same KB by the common test pattern (e.g. `register_prelude(&mut kb);
/// kb.register_standard_builtins(); load::load_all(&mut kb, …)` — `load_all`
/// itself re-enters `register_prelude`). `assert_rule_debruijn_with_nodes` does
/// NOT consult `fact_dedup` (only `assert_fact` does), so an unguarded second
/// call duplicates the rule entry in `by_sort` / `rules_by_functor` / `by_domain`
/// / `discrim`. We therefore early-return when `rules_by_functor[EffectsRuntime]`
/// is non-empty — at prelude-bootstrap time the bridge is the only fact
/// with this functor, so a non-empty entry means the bridge is already
/// installed.
fn emit_effects_runtime_bridge_fact(kb: &mut KnowledgeBase) {
    // Resolve the symbols. Both are unconditionally pre-registered by
    // `register_stdlib_scopes` above (`TypeExtractor.EffectsRows` and
    // `EffectsRuntime`). A missing symbol here means
    // `register_stdlib_scopes` was bypassed or its definitions were
    // accidentally removed — a serious bootstrap regression. Per CLAUDE.md
    // (`avoid fallbacks, better know about errors early`) we panic with a
    // clear message rather than silently skipping the bridge (which would
    // leave the `requires EffectsRuntime[E]` desugaring undischargeable and
    // surface as a confusing "requires unmet" error at every effect-using
    // operation).
    let er_sort_sym = kb.try_resolve_symbol("anthill.prelude.EffectsRuntime").expect(
        "WI-320 bootstrap invariant: anthill.prelude.EffectsRuntime symbol \
         pre-registered by register_stdlib_scopes — see kb/load.rs",
    );
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows").expect(
        "WI-320 bootstrap invariant: anthill.prelude.TypeExtractor.EffectsRows symbol \
         pre-registered by register_stdlib_scopes — see kb/load.rs",
    );

    // Idempotency guard — see doc-comment above. The bridge is the only
    // rule with EffectsRuntime as its head functor at prelude bootstrap,
    // so a non-empty `rules_by_functor` entry means it is already installed.
    if kb.rules_by_functor_iter(er_sort_sym).next().is_some() {
        return;
    }

    let effects_field_sym = kb.intern("Effects");
    let effects_expr_field_sym = kb.intern("effects_expr");

    // The inner wildcard — built as a Global var that
    // `assert_rule_debruijn_with_nodes` closes to `DeBruijn(0)` at rule
    // finalization. The name `expr` is for
    // diagnostic display only (rendered as `?expr` by the pretty-printer's
    // sigil convention); equality / hash-cons key on VarId uses `id` only.
    let expr_var_name = kb.intern("expr");
    let expr_vid = kb.fresh_var(expr_var_name);
    let expr_var_term = kb.alloc(Term::Var(Var::Global(expr_vid)));

    // Build `effects_rows(effects_expr = ?expr)`.
    let effects_rows_term = kb.alloc(Term::Fn {
        functor: effects_rows_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(effects_expr_field_sym, expr_var_term)]),
    });

    // Build the head: `EffectsRuntime(Effects = effects_rows(effects_expr = ?expr))`.
    let head = kb.alloc(Term::Fn {
        functor: er_sort_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(effects_field_sym, effects_rows_term)]),
    });

    // The fact's sort is `EffectsRuntime` itself — same convention as the
    // stdlib's `fact Effect[T = Modify[?]]` (its fact sort is `Effect`).
    let er_sort_as_sort_term = kb.alloc(Term::Fn {
        functor: er_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });

    // Assert via the occurrence-native DeBruijn path to close the Global var to
    // a DeBruijn — fact = rule with empty body (empty occurrence body).
    kb.assert_rule_debruijn_with_nodes(head, vec![], er_sort_as_sort_term, er_sort_as_sort_term, None);
}

/// Create the stdlib scope hierarchy for names the loader references directly.
///
/// Mirrors the structure of `stdlib/anthill/prelude/{list,option}.anthill`
/// and `stdlib/anthill/reflect/reflect.anthill` so that `resolve_symbol("anthill.prelude.List.cons")`
/// etc. return properly-scoped symbols. When the real stdlib is loaded,
/// `scan_definitions` reuses these symbols (idempotent by qualified name).
fn register_stdlib_scopes(kb: &mut KnowledgeBase, global_raw: u32) {
    // Guard: if "anthill" already exists, the whole hierarchy is set up
    if kb.symbols.by_qualified_name.contains_key("anthill") {
        return;
    }

    // anthill namespace
    let anthill_sym = kb.symbols.define("anthill", "anthill", SymbolKind::Namespace, global_raw);
    let anthill_term = kb.alloc(Term::Fn {
        functor: anthill_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(anthill_term.raw(), ScopeInclusion {
        parent_scope_raw: global_raw,
        instantiation_term_raw: global_raw,
        is_enclosing: true,
    });

    // anthill.prelude namespace
    let prelude_sym = kb.symbols.define("prelude", "anthill.prelude", SymbolKind::Namespace, anthill_term.raw());
    let prelude_term = kb.alloc(Term::Fn {
        functor: prelude_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(prelude_term.raw(), ScopeInclusion {
        parent_scope_raw: anthill_term.raw(),
        instantiation_term_raw: anthill_term.raw(),
        is_enclosing: true,
    });

    // anthill.prelude.List sort
    let list_sym = kb.symbols.define("List", "anthill.prelude.List", SymbolKind::Sort, prelude_term.raw());
    let list_term = kb.alloc(Term::Fn {
        functor: list_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(list_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    // WI-521: defined (registers in `by_qualified_name`) but NOT `_global`-imported
    // — the prelude resolves these via the `prelude_qualified` fallback.
    kb.symbols.define("cons", "anthill.prelude.List.cons", SymbolKind::Entity, list_term.raw());
    kb.symbols.define("nil", "anthill.prelude.List.nil", SymbolKind::Entity, list_term.raw());

    // anthill.prelude.Type sort — the opaque, term-backed type handle (WI-361).
    // Its structural forms now live in `TypeExtractor` (below); `Type` itself is
    // a bare `sort Type = ?` with NO constructors. Kept pre-registered so
    // `make_sort_ref_by_name("anthill.prelude.Type")` and the `Eq`/`Lattice`
    // facts riding Type's nominal identity resolve at bootstrap.
    let type_sort_sym = kb.symbols.define("Type", "anthill.prelude.Type", SymbolKind::Sort, prelude_term.raw());
    let type_sort_term = kb.alloc(Term::Fn {
        functor: type_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(type_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });

    // anthill.prelude.TypeExtractor sort — the STRUCTURAL type forms the engine
    // builds as the term backing of a `Type` (WI-361). `make_arrow_type` /
    // `make_denoted` / `make_effects_rows_type` / `make_type_var` /
    // `make_named_tuple_type` / `make_nothing_type` resolve these functors
    // BEFORE stdlib load (at bootstrap), so they are pre-registered here; the
    // stdlib `enum TypeExtractor` re-declares them idempotently. SortRef /
    // Parameterized / Error are COMPUTED-ONLY (a bare sort is `Ref(S)`, a
    // parameterized type `Fn{S, named}`), never built by the engine, so they
    // need no pre-registration here — only the `extract` builtin mints them,
    // post-load, resolving against the stdlib declaration.
    let type_extractor_sort_sym = kb.symbols.define("TypeExtractor", "anthill.prelude.TypeExtractor", SymbolKind::Sort, prelude_term.raw());
    let type_extractor_sort_term = kb.alloc(Term::Fn {
        functor: type_extractor_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(type_extractor_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("Arrow", "anthill.prelude.TypeExtractor.Arrow", SymbolKind::Entity, type_extractor_sort_term.raw());
    kb.symbols.define("TypeVar", "anthill.prelude.TypeExtractor.TypeVar", SymbolKind::Entity, type_extractor_sort_term.raw());
    kb.symbols.define("NamedTuple", "anthill.prelude.TypeExtractor.NamedTuple", SymbolKind::Entity, type_extractor_sort_term.raw());
    kb.symbols.define("Nothing", "anthill.prelude.TypeExtractor.Nothing", SymbolKind::Entity, type_extractor_sort_term.raw());
    kb.symbols.define("Denoted", "anthill.prelude.TypeExtractor.Denoted", SymbolKind::Entity, type_extractor_sort_term.raw());
    kb.symbols.define("ExprCarried", "anthill.prelude.TypeExtractor.ExprCarried", SymbolKind::Entity, type_extractor_sort_term.raw());
    // WI-320 — variant-7 substrate: the EffectExpression-into-Type bridge.
    kb.symbols.define("EffectsRows", "anthill.prelude.TypeExtractor.EffectsRows", SymbolKind::Entity, type_extractor_sort_term.raw());
    // Standalone record for a named-tuple element (anthill.prelude.NamedTupleElement) —
    // built by make_named_tuple_type; lives at prelude scope (not inside an enum).
    kb.symbols.define("NamedTupleElement", "anthill.prelude.NamedTupleElement", SymbolKind::Entity, prelude_term.raw());

    // WI-307 — v1a row-substrate: the EffectExpression algebra entities, the
    // payload `effects_rows` wraps. Pre-registered so `make_arrow_type` can
    // build the canonical `effects_rows(merge(present(…), …, empty_row))`
    // form for the arrow.effects field without depending on stdlib load
    // order. The stdlib `sort.anthill` re-declares the enum; the loader's
    // existing `if defined` guards make the re-declare idempotent.
    let effect_expr_sort_sym = kb.symbols.define("EffectExpression", "anthill.prelude.EffectExpression", SymbolKind::Sort, prelude_term.raw());
    let effect_expr_sort_term = kb.alloc(Term::Fn {
        functor: effect_expr_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(effect_expr_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("empty_row", "anthill.prelude.EffectExpression.empty_row", SymbolKind::Entity, effect_expr_sort_term.raw());
    kb.symbols.define("present", "anthill.prelude.EffectExpression.present", SymbolKind::Entity, effect_expr_sort_term.raw());
    kb.symbols.define("absent", "anthill.prelude.EffectExpression.absent", SymbolKind::Entity, effect_expr_sort_term.raw());
    kb.symbols.define("open", "anthill.prelude.EffectExpression.open", SymbolKind::Entity, effect_expr_sort_term.raw());
    kb.symbols.define("merge", "anthill.prelude.EffectExpression.merge", SymbolKind::Entity, effect_expr_sort_term.raw());

    // anthill.prelude.EffectsRuntime — variant-7 kind anchor (WI-320).
    // Pre-registered so the bridge-fact emission below can resolve the
    // symbol and assert the fact before stdlib loads. The stdlib file
    // `prelude/effects-runtime.anthill` re-declares the sort with its
    // `sort Effects = ?` parameter; the re-declare is idempotent (the
    // loader's existing `if defined` guards skip the symbol). No
    // entities, no operations — scope A is a pure kind anchor.
    let er_sort_sym = kb.symbols.define("EffectsRuntime", "anthill.prelude.EffectsRuntime", SymbolKind::Sort, prelude_term.raw());
    let er_sort_term = kb.alloc(Term::Fn {
        functor: er_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(er_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });

    // anthill.prelude.Option sort
    let option_sym = kb.symbols.define("Option", "anthill.prelude.Option", SymbolKind::Sort, prelude_term.raw());
    let option_term = kb.alloc(Term::Fn {
        functor: option_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(option_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    // WI-521: defined but NOT `_global`-imported (prelude_qualified fallback).
    kb.symbols.define("some", "anthill.prelude.Option.some", SymbolKind::Entity, option_term.raw());
    kb.symbols.define("none", "anthill.prelude.Option.none", SymbolKind::Entity, option_term.raw());

    // WI-644 / proposal 004: PartialEq / PartialOrd are the partial bases that
    // hold the eq/neq and gt/lt/gte/lte OPERATIONS; Eq / Ordered are the lawful /
    // total markers above them (Eq requires PartialEq; Ordered requires Eq,
    // PartialOrd). The bootstrap pre-defines the ops on their base sorts so the
    // builtin-tag registration (register_standard_builtins) and the bare-name
    // fallback resolve to the same symbols the stdlib .anthill files reuse.

    // anthill.prelude.PartialEq sort (operations: eq, neq)
    let partial_eq_sort_sym = kb.symbols.define("PartialEq", "anthill.prelude.PartialEq", SymbolKind::Sort, prelude_term.raw());
    let partial_eq_sort_term = kb.alloc(Term::Fn {
        functor: partial_eq_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(partial_eq_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("eq", "anthill.prelude.PartialEq.eq", SymbolKind::Operation, partial_eq_sort_term.raw());
    kb.symbols.define("neq", "anthill.prelude.PartialEq.neq", SymbolKind::Operation, partial_eq_sort_term.raw());

    // anthill.prelude.Eq — lawful marker (requires PartialEq; no own operations)
    let eq_sort_sym = kb.symbols.define("Eq", "anthill.prelude.Eq", SymbolKind::Sort, prelude_term.raw());
    let eq_sort_term = kb.alloc(Term::Fn {
        functor: eq_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(eq_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });

    // anthill.prelude.PartialOrd sort (operations: gt, lt, gte, lte)
    let partial_ord_sort_sym = kb.symbols.define("PartialOrd", "anthill.prelude.PartialOrd", SymbolKind::Sort, prelude_term.raw());
    let partial_ord_sort_term = kb.alloc(Term::Fn {
        functor: partial_ord_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(partial_ord_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("gt", "anthill.prelude.PartialOrd.gt", SymbolKind::Operation, partial_ord_sort_term.raw());
    kb.symbols.define("lt", "anthill.prelude.PartialOrd.lt", SymbolKind::Operation, partial_ord_sort_term.raw());
    kb.symbols.define("gte", "anthill.prelude.PartialOrd.gte", SymbolKind::Operation, partial_ord_sort_term.raw());
    kb.symbols.define("lte", "anthill.prelude.PartialOrd.lte", SymbolKind::Operation, partial_ord_sort_term.raw());

    // anthill.prelude.Ordered sort (total; operations: compare, max, min; the
    // gt/lt/gte/lte comparison surface is inherited from PartialOrd)
    let ord_sort_sym = kb.symbols.define("Ordered", "anthill.prelude.Ordered", SymbolKind::Sort, prelude_term.raw());
    let ord_sort_term = kb.alloc(Term::Fn {
        functor: ord_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(ord_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("compare", "anthill.prelude.Ordered.compare", SymbolKind::Operation, ord_sort_term.raw());

    // anthill.prelude.Numeric sort (operations: add, sub, mul)
    let num_sort_sym = kb.symbols.define("Numeric", "anthill.prelude.Numeric", SymbolKind::Sort, prelude_term.raw());
    let num_sort_term = kb.alloc(Term::Fn {
        functor: num_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(num_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("add", "anthill.prelude.Numeric.add", SymbolKind::Operation, num_sort_term.raw());
    kb.symbols.define("sub", "anthill.prelude.Numeric.sub", SymbolKind::Operation, num_sort_term.raw());
    kb.symbols.define("mul", "anthill.prelude.Numeric.mul", SymbolKind::Operation, num_sort_term.raw());

    // Proposal 038: register primitive sorts at anthill.prelude scope so
    // stdlib's `sort anthill.prelude.Int64 { ... }` reuses the same Symbol,
    // alias the bare QN for try_resolve_symbol("Int64"), import into _global.
    for &name in PRELUDE_SORTS {
        let qualified = format!("anthill.prelude.{name}");
        let sym = kb.symbols.define(name, &qualified, SymbolKind::Sort, prelude_term.raw());
        let sort_term = kb.alloc(Term::Fn {
            functor: sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
        });
        kb.symbols.add_parent(sort_term.raw(), ScopeInclusion {
            parent_scope_raw: prelude_term.raw(),
            instantiation_term_raw: prelude_term.raw(),
            is_enclosing: true,
        });
        kb.symbols.by_qualified_name.insert(name.to_string(), sym);
        kb.symbols.add_import(global_raw, name, sym);
    }
    // BigInt conversion operations — pre-registered so stdlib body reuses them.
    let bigint_sym = kb.symbols.by_qualified_name["anthill.prelude.BigInt"];
    let bigint_term = kb.alloc(Term::Fn {
        functor: bigint_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.define("to_bigint", "anthill.prelude.BigInt.to_bigint", SymbolKind::Operation, bigint_term.raw());
    kb.symbols.define("to_int", "anthill.prelude.BigInt.to_int", SymbolKind::Operation, bigint_term.raw());

    // anthill.reflect namespace
    let reflect_sym = kb.symbols.define("reflect", "anthill.reflect", SymbolKind::Namespace, anthill_term.raw());
    let reflect_term = kb.alloc(Term::Fn {
        functor: reflect_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(reflect_term.raw(), ScopeInclusion {
        parent_scope_raw: anthill_term.raw(),
        instantiation_term_raw: anthill_term.raw(),
        is_enclosing: true,
    });
    // WI-521: the reflection `*Info` sorts are defined (registered in
    // `by_qualified_name`) but NOT `_global`-imported — reflection code reaches
    // them by explicit import (`reflect/typing.anthill`) or self-scope.
    kb.symbols.define("SortInfo", "anthill.reflect.SortInfo", SymbolKind::Entity, reflect_term.raw());
    kb.symbols.define("FieldInfo", "anthill.reflect.FieldInfo", SymbolKind::Entity, reflect_term.raw());
    kb.symbols.define("OperationInfo", "anthill.reflect.OperationInfo", SymbolKind::Entity, reflect_term.raw());
    kb.symbols.define("EntityInfo", "anthill.reflect.EntityInfo", SymbolKind::Entity, reflect_term.raw());
    kb.symbols.define("SortRequiresInfo", "anthill.reflect.SortRequiresInfo", SymbolKind::Entity, reflect_term.raw());
    kb.symbols.define("SortProvidesInfo", "anthill.reflect.SortProvidesInfo", SymbolKind::Entity, reflect_term.raw());
    kb.symbols.define("SortView", "anthill.reflect.SortView", SymbolKind::Entity, reflect_term.raw());
    // WI-040: the literal carriers are DEFINED here (registers them in
    // `by_qualified_name`) but NOT `_global`-imported — they resolve directly via
    // `kernel_vocab_qualified`. So the returned symbols are intentionally unused.
    kb.symbols.define("SetLiteral", "anthill.reflect.SetLiteral", SymbolKind::Entity, reflect_term.raw());
    kb.symbols.define("TupleLiteral", "anthill.reflect.TupleLiteral", SymbolKind::Entity, reflect_term.raw());
    kb.symbols.define("ListLiteral", "anthill.reflect.ListLiteral", SymbolKind::Entity, reflect_term.raw());
    // WI-390 — Positioned(pos, internal): a local-binder reference carried with its
    // absolute binding-site identity (`pos`) so two distinct locals don't collide as
    // hash-consed terms. Built by `make_positioned`; leaf-only; unifies structurally.
    kb.symbols.define("Positioned", "anthill.reflect.Positioned", SymbolKind::Entity, reflect_term.raw());

    // anthill.reflect.Expr sort + entities
    let expr_sym = kb.symbols.define("Expr", "anthill.reflect.Expr", SymbolKind::Sort, reflect_term.raw());
    let expr_term = kb.alloc(Term::Fn {
        functor: expr_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(expr_term.raw(), ScopeInclusion {
        parent_scope_raw: reflect_term.raw(),
        instantiation_term_raw: reflect_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("match_expr", "anthill.reflect.Expr.match_expr", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("if_expr", "anthill.reflect.Expr.if_expr", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("let_expr", "anthill.reflect.Expr.let_expr", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("lambda_expr", "anthill.reflect.Expr.lambda_expr", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("proof_stmt", "anthill.reflect.Expr.proof_stmt", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("apply", "anthill.reflect.Expr.apply", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("ho_apply", "anthill.reflect.Expr.ho_apply", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("constructor", "anthill.reflect.Expr.constructor", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("dot_apply", "anthill.reflect.Expr.dot_apply", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("var_ref", "anthill.reflect.Expr.var_ref", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("int_lit", "anthill.reflect.Expr.int_lit", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("bigint_lit", "anthill.reflect.Expr.bigint_lit", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("float_lit", "anthill.reflect.Expr.float_lit", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("string_lit", "anthill.reflect.Expr.string_lit", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("bool_lit", "anthill.reflect.Expr.bool_lit", SymbolKind::Entity, expr_term.raw());

    // anthill.reflect.Pattern sort + entities
    let pattern_sym = kb.symbols.define("Pattern", "anthill.reflect.Pattern", SymbolKind::Sort, reflect_term.raw());
    let pattern_term = kb.alloc(Term::Fn {
        functor: pattern_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(pattern_term.raw(), ScopeInclusion {
        parent_scope_raw: reflect_term.raw(),
        instantiation_term_raw: reflect_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("var_pattern", "anthill.reflect.Pattern.var_pattern", SymbolKind::Entity, pattern_term.raw());
    kb.symbols.define("tuple_pattern", "anthill.reflect.Pattern.tuple_pattern", SymbolKind::Entity, pattern_term.raw());
    kb.symbols.define("named_tuple_pattern", "anthill.reflect.Pattern.named_tuple_pattern", SymbolKind::Entity, pattern_term.raw());
    kb.symbols.define("constructor_pattern", "anthill.reflect.Pattern.constructor_pattern", SymbolKind::Entity, pattern_term.raw());
    kb.symbols.define("literal_pattern", "anthill.reflect.Pattern.literal_pattern", SymbolKind::Entity, pattern_term.raw());
    kb.symbols.define("wildcard", "anthill.reflect.Pattern.wildcard", SymbolKind::Entity, pattern_term.raw());

    // anthill.reflect standalone entities for expressions
    kb.symbols.define("MatchBranch", "anthill.reflect.MatchBranch", SymbolKind::Entity, reflect_term.raw());
    kb.symbols.define("ApplyArg", "anthill.reflect.ApplyArg", SymbolKind::Entity, reflect_term.raw());
    // WI-445: a `case Foo(field: pat)` named sub-pattern rides a NamedPattern
    // (the same reflect entity `named_tuple_pattern` uses); register it
    // programmatically so `ExprBuilderSyms` can resolve it during load.
    kb.symbols.define("NamedPattern", "anthill.reflect.NamedPattern", SymbolKind::Entity, reflect_term.raw());

    // anthill.reflect.TypedExpr sort
    let typed_expr_sym = kb.symbols.define("TypedExpr", "anthill.reflect.TypedExpr", SymbolKind::Sort, reflect_term.raw());
    let typed_expr_term = kb.alloc(Term::Fn {
        functor: typed_expr_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(typed_expr_term.raw(), ScopeInclusion {
        parent_scope_raw: reflect_term.raw(),
        instantiation_term_raw: reflect_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("typed", "anthill.reflect.TypedExpr.typed", SymbolKind::Entity, typed_expr_term.raw());

    // anthill.reflect.typing namespace
    let typing_sym = kb.symbols.define("typing", "anthill.reflect.typing", SymbolKind::Namespace, reflect_term.raw());
    let typing_term = kb.alloc(Term::Fn {
        functor: typing_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(typing_term.raw(), ScopeInclusion {
        parent_scope_raw: reflect_term.raw(),
        instantiation_term_raw: reflect_term.raw(),
        is_enclosing: true,
    });

    // anthill.reflect.feed namespace (WI-352) — created here so the `provenance`
    // builtin can register before stdlib/anthill/reflect/feed.anthill loads.
    let feed_sym = kb.symbols.define("feed", "anthill.reflect.feed", SymbolKind::Namespace, reflect_term.raw());
    let feed_term = kb.alloc(Term::Fn {
        functor: feed_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(feed_term.raw(), ScopeInclusion {
        parent_scope_raw: reflect_term.raw(),
        instantiation_term_raw: reflect_term.raw(),
        is_enclosing: true,
    });

    // anthill.kernel namespace — resolver primitives (proposal 033).
    // Pre-declared here so that the loader's resolve_symbol calls find
    // these names with proper scoping when stdlib/anthill/kernel/ loads.
    let kernel_sym = kb.symbols.define("kernel", "anthill.kernel", SymbolKind::Namespace, anthill_term.raw());
    let kernel_term = kb.alloc(Term::Fn {
        functor: kernel_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(kernel_term.raw(), ScopeInclusion {
        parent_scope_raw: anthill_term.raw(),
        instantiation_term_raw: anthill_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("push_choice", "anthill.kernel.push_choice", SymbolKind::Operation, kernel_term.raw());
    kb.symbols.define("or", "anthill.kernel.or", SymbolKind::Operation, kernel_term.raw());

    // WI-521: the user-facing PRELUDE (cons / nil / some / none, the arithmetic
    // and comparison operator targets eq / neq / gt / lt / gte / lte / add / sub /
    // mul / to_bigint / to_int, and the logic operators not / or) is NOT
    // `_global`-imported. It resolves via the lowest-precedence `prelude_qualified`
    // fallback in `remap_name_str` / `resolve_name_in_kb_opt`: a user's local
    // definition or explicit import always wins, and the prelude name can never go
    // AMBIGUOUS against a user name (the failure mode the old flat `_global`
    // injection had — see the WI-476 collision blocklist that WI-040 removed).
    //
    // The reflection `*Info` result sorts (SortInfo / FieldInfo / …) also resolve
    // via `prelude_qualified` (a reflection vocabulary, queried bare by the
    // reflect bridge / CLI). Their `define` calls remain (registering them in
    // `by_qualified_name`, which the fallback looks up); only the `_global` imports
    // are gone.
}

// ══════════════════════════════════════════════════════════════════
// Phase 2: Load into KB
// ══════════════════════════════════════════════════════════════════

/// Load a parsed file into the knowledge base.
///
/// Scans definitions first, then loads facts into the KB.
pub fn load(
    kb: &mut KnowledgeBase,
    parsed: &ParsedFile,
    resolver: &dyn SourceResolver,
) -> Result<LoadResult, Vec<LoadError>> {
    register_prelude(kb);
    let mut all_errors = scan_definitions(kb, &[parsed]);
    kb.resolve_builtins();
    let mut loaded_paths = HashSet::new();
    let mut all_sorts = Vec::new();
    let mut all_fact_ids = Vec::new();
    match load_with_visited(kb, parsed, resolver, &mut loaded_paths) {
        Ok(result) => {
            all_sorts.extend(result.defined_sorts);
            all_fact_ids.extend(result.fact_rule_ids);
        }
        Err(errs) => all_errors.extend(errs),
    }
    resolve_instantiations(kb);
    if all_errors.is_empty() {
        Ok(LoadResult { defined_sorts: all_sorts, fact_rule_ids: all_fact_ids, warnings: Vec::new() })
    } else {
        Err(all_errors)
    }
}

/// Load multiple parsed files into the same knowledge base, including the
/// prelude. Scans ALL files for definitions first, then loads them, so that
/// cross-file references resolve correctly regardless of load order.
pub fn load_all(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<LoadResult, Vec<LoadError>> {
    register_prelude(kb);
    load_phase(kb, files, resolver)
}

/// Alias of [`load_all`]. Named for clarity when loading stdlib as the first
/// phase of an incremental workflow; subsequent files can then be added via
/// [`load_incremental`] without reprocessing already-finalized facts.
pub fn load_stdlib(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<LoadResult, Vec<LoadError>> {
    load_all(kb, files, resolver)
}

/// Load additional files on top of an already-populated KB. Skips
/// `register_prelude`. Relies on `resolve_instantiations` being idempotent
/// (`resolved_requires_facts` guard) so stdlib facts are not retracted or
/// reasserted. The returned `LoadResult.defined_sorts` contains only sorts
/// defined in `files`.
pub fn load_incremental(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<LoadResult, Vec<LoadError>> {
    load_phase(kb, files, resolver)
}

fn load_phase(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<LoadResult, Vec<LoadError>> {
    load_phase_inner(kb, files, resolver).map(|(merged, _)| merged)
}

/// Same as [`load_phase`] but also returns each file's individual
/// `LoadResult`, parallel to `files`. Used by `IndexedFileStore` so the
/// caller can pair each file's `fact_rule_ids` with its on-disk path
/// without losing the per-file boundary information that the merged
/// `LoadResult` discards.
pub fn load_all_per_file(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<(LoadResult, Vec<LoadResult>), Vec<LoadError>> {
    register_prelude(kb);
    load_phase_inner(kb, files, resolver)
}

/// Proposal 039 / WI-084 — the const purity gate. An anthill-bodied `const`
/// must fold to a value PURELY: its body may not invoke an effectful operation
/// (one with a non-empty declared effect row — e.g. an allocator's
/// `Modify[result]`, per 027.1). A const denotes one MEMOIZED value shared by
/// every reference, so an effectful body is unsound (the generativity hazard:
/// `Cell.new()` ≠ `Cell.new()`). Checked statically at load — by now every
/// operation's `OperationInfo` effect row is present. Bodyless (host-supplied)
/// consts have no body to check and are trusted. Returns one `LoadError` per
/// impure const.
fn check_const_purity(kb: &KnowledgeBase) -> Vec<LoadError> {
    // Snapshot (sym, body) so the walk can re-borrow `kb` for effect lookups.
    let consts: Vec<(Symbol, std::rc::Rc<NodeOccurrence>)> = kb
        .const_bodies_iter()
        .map(|(s, n)| (s, std::rc::Rc::clone(n)))
        .collect();
    let mut errors = Vec::new();
    for (sym, body) in &consts {
        if let Err(reason) = const_node_is_pure(kb, body) {
            errors.push(LoadError::Other {
                message: format!(
                    "const `{}` has a non-foldable body — it {reason}. A const denotes a single \
                     memoized value, so its body must be pure (empty effect row); use an \
                     operation (which can declare effects) if you need an effectful computation.",
                    kb.qualified_name_of(*sym),
                ),
            });
        }
    }
    errors
}

/// Recursively verify a const body occurrence is pure. CONSERVATIVE by
/// construction: only forms whose purity is statically provable are accepted;
/// any unrecognized or dynamically-dispatched form (higher-order / dot calls,
/// generic instantiation, the post-elaboration `*Within` forms a raw const body
/// never contains) is REJECTED — so the gate can never silently admit an effect.
/// Returns `Err(reason)` for the first offending form (reason is a fragment that
/// reads after "it …", e.g. "calls effectful operation `Cell.new`").
fn const_node_is_pure(kb: &KnowledgeBase, occ: &std::rc::Rc<NodeOccurrence>) -> Result<(), String> {
    // Only Expr-kind occurrences compute; Pattern / Type carry no effects.
    let expr = match &occ.kind {
        node_occurrence::NodeKind::Expr { expr, .. } => expr,
        _ => return Ok(()),
    };
    match expr {
        // Pure leaves. (`Bottom`/`Var` won't fold to a value, but neither is an
        // effect — a non-reducing body fails the fold separately.)
        Expr::Const(_) | Expr::Var(_) | Expr::Bottom => Ok(()),
        // A bare reference: a nullary OPERATION reference is a zero-arg call (so
        // an effectful one is impure); a multi-arg op ref is eta (a pure closure
        // value); a const / constructor / param ref is pure.
        Expr::Ref(s) | Expr::Ident(s) | Expr::VarRef { name: s } => const_ref_is_pure(kb, *s),
        // A lambda is a pure VALUE — folding yields a closure; its body's effects
        // (if any) are deferred to application, not performed at fold.
        Expr::Lambda { .. } => Ok(()),
        // Pure composition / construction: recurse into the evaluated children.
        Expr::Let { value, body, .. } => {
            const_node_is_pure(kb, value)?;
            const_node_is_pure(kb, body)
        }
        Expr::If { condition, then_branch, else_branch } => {
            const_node_is_pure(kb, condition)?;
            const_node_is_pure(kb, then_branch)?;
            const_node_is_pure(kb, else_branch)
        }
        Expr::Match { scrutinee, branches } => {
            const_node_is_pure(kb, scrutinee)?;
            for b in branches {
                if let Some(g) = &b.guard {
                    const_node_is_pure(kb, g)?;
                }
                const_node_is_pure(kb, &b.body)?;
            }
            Ok(())
        }
        Expr::TupleLit { positional, named } => {
            for c in positional {
                const_node_is_pure(kb, c)?;
            }
            for (_, c) in named {
                const_node_is_pure(kb, c)?;
            }
            Ok(())
        }
        Expr::ListLit(items) | Expr::SetLit(items) => {
            for c in items {
                const_node_is_pure(kb, c)?;
            }
            Ok(())
        }
        Expr::Constructor { pos_args, named_args, .. } => {
            // Entity construction is pure; check the field expressions.
            for c in pos_args {
                const_node_is_pure(kb, c)?;
            }
            for (_, c) in named_args {
                const_node_is_pure(kb, c)?;
            }
            Ok(())
        }
        // A direct operation call: the callee must be effect-free, and so must
        // every argument.
        Expr::Apply { functor, pos_args, named_args, .. } => {
            const_callee_is_pure(kb, *functor)?;
            for c in pos_args {
                const_node_is_pure(kb, c)?;
            }
            for (_, c) in named_args {
                const_node_is_pure(kb, c)?;
            }
            Ok(())
        }
        // WI-538: an in-body proof is a type-level construct (no runtime
        // effect) — the const's value is the continuation's. Check the
        // conclude goal and the body.
        Expr::Proof { conclude, body, .. } => {
            if let Some(c) = conclude {
                const_node_is_pure(kb, c)?;
            }
            const_node_is_pure(kb, body)
        }
        // Everything else — higher-order / dot dispatch, generic instantiation,
        // and the post-elaboration `*Within` / requirement forms (which a raw,
        // un-elaborated const body never contains) — cannot be proven pure here.
        other => Err(format!(
            "uses a form whose purity cannot be statically verified ({})",
            const_expr_form_name(other),
        )),
    }
}

/// A callee in APPLY position is pure unless it is an operation with a non-empty
/// declared effect row.
fn const_callee_is_pure(kb: &KnowledgeBase, functor: Symbol) -> Result<(), String> {
    if kb.kind_of(functor) == Some(crate::intern::SymbolKind::Operation) {
        if let Some(info) = crate::kb::op_info::lookup_operation_info(kb, functor) {
            if !info.effects.is_empty() {
                return Err(format!("calls effectful operation `{}`", kb.qualified_name_of(functor)));
            }
        }
    }
    Ok(())
}

/// A bare REFERENCE is pure unless it names a NULLARY operation with effects (a
/// zero-arg effectful call). A multi-arg op ref is eta — a pure closure value.
fn const_ref_is_pure(kb: &KnowledgeBase, sym: Symbol) -> Result<(), String> {
    if kb.kind_of(sym) == Some(crate::intern::SymbolKind::Operation) {
        if let Some(info) = crate::kb::op_info::lookup_operation_info(kb, sym) {
            if info.params.is_empty() && !info.effects.is_empty() {
                return Err(format!(
                    "references effectful nullary operation `{}` (a zero-arg call)",
                    kb.qualified_name_of(sym)
                ));
            }
        }
    }
    Ok(())
}

/// Human-readable name for an `Expr` form rejected by the purity gate.
fn const_expr_form_name(e: &Expr) -> &'static str {
    match e {
        Expr::HoApply { .. } | Expr::HoApplyWithin { .. } => "higher-order application",
        Expr::DotApply { .. } => "method/dot call",
        Expr::Instantiation { .. } => "generic instantiation",
        Expr::ApplyWithin { .. } => "apply-within",
        Expr::ConstructorWithin { .. } => "constructor-within",
        Expr::LambdaWithin { .. } => "lambda-within",
        Expr::RequirementAtSort { .. } | Expr::ConstructRequirement { .. } => "requirement form",
        _ => "unsupported expression form",
    }
}

#[allow(unused_assignments)]
fn load_phase_inner(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<(LoadResult, Vec<LoadResult>), Vec<LoadError>> {
    // WI-659 — reset the SortAlias index at the START of every load phase. It is
    // rebuilt at this phase's type-check (`build_sort_alias_index`); clearing it
    // first means load-time `resolve_sort_alias` calls in this phase fall back to
    // the scan — seeing THIS phase's freshly-asserted aliases — instead of reading a
    // stale index left by a prior phase. Load-bearing for `load_incremental`:
    // `resolve_sort_alias`'s fast path has no fallback-on-miss, so a phase-2 alias
    // absent from the phase-1 index would otherwise silently resolve to `None`/the
    // wrong var. A no-op on the first (or only) load — the field starts `None`.
    kb.sort_alias_index = None;
    // WI-660 — same reset for the SortProvidesInfo (provider) index, same reason:
    // it is rebuilt at this phase's type-check (`build_provides_index`), and the
    // dispatch/coherence consumers use it with no fallback-on-miss (a `Some` index
    // is trusted whole), so a stale index left by a prior phase would silently hide
    // this phase's freshly-asserted `provides` facts. Clearing it first makes those
    // load-time lookups scan the live relation until the rebuild. NB this is the
    // ONLY invalidation the index needs: `SortProvidesInfo` is `constant` (053/WI-665),
    // so it never mutates at RUNTIME — no per-fact-mutation drop (see `provides_index`).
    kb.provides_index = None;
    // WI-671 — same reset for the SortInfo index. Rebuilt at this phase's type-check
    // (`build_sort_info_index`); clearing it first makes this phase's load-time SortInfo
    // lookups fall back to the live scan (seeing THIS phase's freshly-asserted SortInfo
    // facts) instead of a stale index from a prior phase — load-bearing for
    // `load_incremental`. SortInfo is frozen after the file-loading loop and untouched
    // by eq_derive, so unlike `provides_index` this is the ONLY invalidation it needs.
    kb.sort_info_index = None;

    // WI-233: per-sub-phase timing, gated by ANTHILL_LOAD_TIMING=1.
    // Surfaces which step of the load pipeline dominates wall time
    // (scan / load / resolve / witnesses / typecheck / req_insertion).
    let timing = std::env::var("ANTHILL_LOAD_TIMING").map(|v| v == "1").unwrap_or(false);
    let mut t = std::time::Instant::now();
    macro_rules! mark {
        ($label:expr) => {
            if timing {
                let now = std::time::Instant::now();
                eprintln!("[load_timing]   {}: {:?}", $label, now.duration_since(t));
                t = now;
            }
        };
    }

    let mut all_errors = scan_definitions(kb, files);
    // WI-345: non-fatal diagnostics, accumulated parallel to `all_errors`.
    // Lint passes (e.g. WI-346 requires-shadow, below) extend this; it rides
    // out on the merged `LoadResult` when the load succeeds.
    let mut all_warnings: Vec<LoadWarning> = Vec::new();
    mark!("scan_definitions");
    kb.resolve_builtins();
    mark!("resolve_builtins");
    register_implicit_prelude_effects(kb);
    mark!("register_implicit_prelude_effects");

    let item_timing = std::env::var("ANTHILL_ITEM_TIMING").map(|v| v == "1").unwrap_or(false);
    if item_timing { reset_item_timings(); }
    let mut loaded_paths = HashSet::new();
    let mut all_sorts = Vec::new();
    let mut all_fact_ids = Vec::new();
    let mut per_file: Vec<LoadResult> = Vec::with_capacity(files.len());
    for parsed in files {
        match load_with_visited(kb, parsed, resolver, &mut loaded_paths) {
            Ok(result) => {
                all_sorts.extend(result.defined_sorts.clone());
                all_fact_ids.extend(result.fact_rule_ids.clone());
                per_file.push(result);
            }
            Err(errs) => {
                all_errors.extend(errs);
                per_file.push(LoadResult::default());
            }
        }
    }
    mark!(&format!("load_with_visited x {}", files.len()));
    if item_timing {
        print_item_timings(&format!("load_with_visited x {}", files.len()));
    }
    resolve_instantiations(kb);
    mark!("resolve_instantiations");
    register_requires_axiom_witnesses(kb);
    mark!("register_requires_axiom_witnesses");
    register_induction_axiom_witnesses(kb);
    mark!("register_induction_axiom_witnesses");
    register_specialization_witnesses(kb);
    mark!("register_specialization_witnesses");
    // WI-240 — precompute the per-impl-sort operations table before
    // typing, so the typer's spec-op dispatch reads it via
    // `kb.sort_ops_lookup` instead of the string-concat fallback.
    build_sort_ops_table(kb);
    mark!("build_sort_ops_table");
    // WI-352/WI-353: derive `flow(kind, from, to)` facts from operation bodies
    // BEFORE op-body type-checking, because the typer's operation-boundary
    // masking (WI-353, `region::op_boundary_effects`) consumes them via
    // `keep_modify` to re-key a callback parameter's `Modify` to the op's data —
    // so the facts must be asserted before the typer runs. The pass walks body
    // STRUCTURE only (apply/match occurrences + `arg_places`), needs no types,
    // and runs on the pre-`[simp]` bodies; feeds key on argument positions, which
    // dispatch / `[simp]` rewrites preserve, so the derived facts are stable
    // across the rewrite. The facts are auxiliary (own namespace/functor) and do
    // not perturb resolution.
    super::flow_derive::run(kb);
    mark!("flow_derive::run");
    // WI-283: `[simp]` firing over operation bodies now runs *inside* the
    // typer (`typing::build_type`), where it is type-directed — children
    // are typed first, so `min_sort`/`requires` guards have the operand's
    // type in hand. The typer is tree-producing: it writes each rewritten
    // (redex-free) body back via `set_op_body_node` before returning, so
    // req_insertion, eval, and codegen see the rewritten form. The former
    // pre-typer `simp_rewrite::run` pass (WI-277, guard-free, type-blind)
    // is retired from the pipeline; its machinery is reused by the typer.
    // WI-429: formation sweep for stored `RigidTypeProjection` terms — a
    // malformed projection in a position the typer never eliminates (entity
    // field types, fact/rule type slots) must fail the load, not sit silent.
    // Runs once requires/provides info is complete (after
    // `resolve_instantiations`), before the typer (whose elimination sites
    // re-validate the eliminated subset with the same logic).
    all_errors.extend(super::typing::validate_rigid_projection_formations(kb));
    mark!("validate_rigid_projection_formations");
    all_errors.extend(super::typing::type_check_sorts(kb, &all_sorts));
    mark!(&format!("type_check_sorts ({} sorts)", all_sorts.len()));
    // WI-231: the typer tagged each spec-op call site's occurrence
    // with a `CallClass`; run the requirement-insertion pass to emit
    // the IR rewrites into `kb.dispatch_rewrites`. Skipping this call
    // would leave the IR in the typed-but-unelaborated state (useful
    // for alternative codegen targets). WI-325: also returns any
    // `MissingRequiresForSpecOp` diagnostics from `UnresolvedSpecOp`
    // tags (typer-detected abstract spec-op calls without a covering
    // `requires`); merged into the load-time error list.
    let req_errors = super::req_insertion::run(kb);
    for err in req_errors {
        all_errors.push(err.to_load_error(kb));
    }
    mark!("req_insertion::run");
    // WI-343: provider-side requires coverage. For each `fact Spec[X]`,
    // every spec-level `requires` of Spec (at the provision's bindings)
    // must itself be satisfied — else the satisfaction fact is unsound.
    all_errors.extend(super::typing::check_provider_requires(kb));
    mark!("check_provider_requires");
    // WI-363: provider-side operation coverage — the op-level twin of the
    // above. For each `fact Spec[X]`, every operation Spec declares must be
    // backed by a spec default (body/derivation rule) or an op X supplies;
    // an unbacked op makes the satisfaction fact unsound (calls resolve to
    // nothing at runtime). Load-blocking.
    all_errors.extend(super::typing::check_provider_operations(kb));
    mark!("check_provider_operations");
    // WI-664: derive composite Eq/NonEq classification. Builds the field-wise-eq
    // carrier set (`field_wise_noneq_carriers`, read by the resolver and
    // interpreter to compare a Float-containing composite FIELD-WISE) and asserts
    // the derived `NonEq`+`PartialEq` provision facts for each such composite.
    // Placed AFTER the provider-coverage checks — a derived `NonEq`'s `nonEqRefl`
    // witness is a propagated classification, not a hand-declared op held to
    // backing — and BEFORE `check_eq_noneq_exclusive`, so a user `provides
    // Eq[Point]` over a Float-containing `Point` conflicts with the derived
    // `NonEq[Point]` and is rejected (the WI-658 route, "composes automatically").
    // WI-660 — `eq_derive::run` both READS the provider relation (`sort_provides`, to
    // skip an already-provided derivation) AND ASSERTS new `SortProvidesInfo` facts
    // (derived `NonEq`/`PartialEq` for Float-containing composites) in the SAME loop.
    // Drop the index to `None` FIRST so those reads hit the live scan and see the facts
    // eq_derive is asserting as it goes (the pre-WI-660 behaviour). A `Some` index —
    // built at `type_check_sorts` start, before any of this — would be stale mid-loop
    // and miss a just-derived edge (e.g. re-deriving a duplicate `NonEq` for two
    // alias-distinct symbols of one composite sort).
    kb.provides_index = None;
    super::eq_derive::run(kb);
    // Rebuild now the relation is frozen again: eq_derive is the LAST load pass to
    // assert `SortProvidesInfo`, so the post-eq_derive checks below
    // (`check_eq_noneq_exclusive`, `check_use_site_requires_eq`) and the persisted
    // runtime index (`sort_provides` from the resolver's simp guard) all read a COMPLETE
    // index — else a Float-composite key like `Map[K = Pt]` would silently miss its
    // derived `NonEq` and load clean. `constant` (WI-665) forbids only EVAL-time
    // mutation; this LOAD-time derivation is legitimate, hence the explicit
    // null-then-rebuild here rather than the eval guard.
    super::typing::build_provides_index(kb);
    mark!("eq_derive::run");
    // WI-658: Eq ⊥ NonEq — a carrier that provides both the lawful (reflexive)
    // Eq and the witnessed non-reflexive NonEq is contradictory. Opt-in: does
    // nothing for a carrier that declares neither. Load-blocking.
    all_errors.extend(super::typing::check_eq_noneq_exclusive(kb));
    mark!("check_eq_noneq_exclusive");
    // WI-644: use-site `requires Eq` — an entity field type `Map[K = Float]` (a
    // parametric sort `requires Eq[K]` bound to a `NonEq` carrier) is a load error,
    // not a silent wrong answer. After eq_derive so a Float-composite's derived
    // NonEq is visible.
    all_errors.extend(super::typing::check_use_site_requires_eq(kb));
    mark!("check_use_site_requires_eq");
    // WI-347: operation-override refinement — a carrier's own op overriding a
    // spec op must refine it (effects no wider; pre/post next). Load-blocking
    // (unsound override), so it lands in `all_errors`.
    all_errors.extend(super::typing::check_override_refinement(kb));
    mark!("check_override_refinement");
    // WI-431 (B): instance-fact op-binding signature validation — a bound op
    // (`fact Combiner[T = Tag, combine = wrongOp]`) must match the spec op's
    // signature with the carrier substituted. Load-blocking (a mis-bound op would
    // dispatch to a wrongly-typed impl via WI-431 increments 2/4).
    all_errors.extend(super::typing::check_instance_fact_op_signatures(kb));
    mark!("check_instance_fact_op_signatures");
    // Proposal 039 / WI-084: the const purity gate. An anthill-bodied const whose
    // body invokes an effectful operation (e.g. an allocator) is load-blocking —
    // memoizing an effectful value is unsound. Runs after all operations load, so
    // every effect row is queryable.
    all_errors.extend(check_const_purity(kb));
    mark!("check_const_purity");
    // WI-346: requires-shadow lint — advisory (non-fatal), so it lands in
    // `all_warnings`, not `all_errors`. A legal-but-suspicious same-named op on
    // a `requires`-user (which does NOT override) should be flagged, not block.
    all_warnings.extend(check_requires_shadows(kb));
    mark!("check_requires_shadows");
    // WI-023: post-load integrity-constraint check. Every quantified constraint
    // registered as a guard (via `load_constraint`) is evaluated against the now-
    // complete fact set; a violation is load-blocking, and (WI-513) a constraint
    // whose LogicalQuery the shared lowerer cannot handle is surfaced loudly as a
    // load-blocking error rather than silently passing. No-op when no guards are
    // registered (the common case — no quantified constraints).
    for check in kb.check_all_guards() {
        match check {
            super::GuardCheck::Holds => {}
            super::GuardCheck::Violated(label) => {
                all_errors.push(LoadError::ConstraintViolated { label });
            }
            super::GuardCheck::Unsupported(label, detail) => {
                all_errors.push(LoadError::ConstraintLoweringFailed { label, detail });
            }
            // WI-628: a constraint whose proof search truncated at the depth
            // limit is undecided — surface loudly (load-blocking), never a
            // silent pass.
            super::GuardCheck::Undecidable(label, detail) => {
                all_errors.push(LoadError::ConstraintUndecidable { label, detail });
            }
        }
    }
    mark!("check_all_guards");
    if all_errors.is_empty() {
        Ok((
            LoadResult { defined_sorts: all_sorts, fact_rule_ids: all_fact_ids, warnings: all_warnings },
            per_file,
        ))
    } else {
        Err(all_errors)
    }
}

/// Internal: load with cycle detection via `loaded_paths`.
fn load_with_visited(
    kb: &mut KnowledgeBase,
    parsed: &ParsedFile,
    resolver: &dyn SourceResolver,
    loaded_paths: &mut HashSet<String>,
) -> Result<LoadResult, Vec<LoadError>> {
    let global = kb.make_name_term("_global");
    let mut loader = Loader::new(kb, parsed, resolver, loaded_paths, global);
    loader.load_items(&parsed.items, None);

    let result = LoadResult {
        defined_sorts: loader.defined_sorts,
        fact_rule_ids: loader.fact_rule_ids,
        warnings: Vec::new(),
    };
    if loader.errors.is_empty() {
        Ok(result)
    } else {
        Err(loader.errors)
    }
}

// ══════════════════════════════════════════════════════════════════
// Phase 3: Resolve instantiation bindings
// ══════════════════════════════════════════════════════════════════

/// Complete all ParameterizedType substitutions in SortRequiresInfo facts.
///
/// Called after load: (1) builds base substitutions from SortInfo facts,
/// (2) for each SortRequiresInfo fact, completes spec_inst with explicit bindings
/// and auto-bound same-named operations from the requiring sort's scope.
pub fn resolve_instantiations(kb: &mut KnowledgeBase) {
    build_base_substitutions(kb);
    resolve_requires_bindings(kb);
}

/// Build base substitution for each sort from its SortInfo fact.
///
/// The base substitution maps every slot (parameter + operation) to itself:
/// `{T → Ref(T), combine → Ref(combine), identity → Ref(identity)}`.
fn build_base_substitutions(kb: &mut KnowledgeBase) {
    let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        Some(sym) => sym,
        None => return,
    };

    let rule_ids = kb.rules_by_functor(sort_info_sym);
    let name_sym = kb.intern("name");
    let parameters_sym = kb.intern("parameters");
    let operations_sym = kb.intern("operations");
    let mut sort_entries: Vec<(Symbol, Vec<(Symbol, TermId)>)> = Vec::new();

    for rid in rule_ids {
        if !kb.is_fact(rid) {
            continue; // skip rules, only process facts
        }
        let Some(head) = kb.fact_head_term(rid) else { continue };
        let term = kb.get_term(head).clone();
        if let Term::Fn { named_args, .. } = term {
            let sort_functor_sym = named_args.iter()
                .find(|(s, _)| *s == name_sym)
                .and_then(|(_, tid)| match kb.get_term(*tid) {
                    Term::Ref(sym) => Some(*sym),
                    _ => None,
                });

            if let Some(sym) = sort_functor_sym {
                if kb.sort_base_subst(sym).is_some() {
                    continue;
                }
            }

            let params_list_tid = named_args.iter()
                .find(|(s, _)| *s == parameters_sym)
                .map(|(_, tid)| *tid);

            let ops_list_tid = named_args.iter()
                .find(|(s, _)| *s == operations_sym)
                .map(|(_, tid)| *tid);

            if let Some(sort_sym) = sort_functor_sym {
                let mut base_subst = Vec::new();

                // Collect params
                if let Some(list_tid) = params_list_tid {
                    collect_ref_list(kb, list_tid, &mut base_subst);
                }

                // Collect operations
                if let Some(list_tid) = ops_list_tid {
                    collect_ref_list(kb, list_tid, &mut base_subst);
                }

                sort_entries.push((sort_sym, base_subst));
            }
        }
    }

    for (sym, subst) in sort_entries {
        kb.set_sort_base_subst(sym, subst);
    }
}

/// Walk a cons-list and collect (sym, Ref(sym)) pairs for each Ref element.
fn collect_ref_list(kb: &mut KnowledgeBase, list_tid: TermId, out: &mut Vec<(Symbol, TermId)>) {
    let head_sym = kb.intern("head");
    let tail_sym = kb.intern("tail");
    let nil_sym = kb.resolve_symbol("anthill.prelude.List.nil");
    let cons_sym = kb.resolve_symbol("anthill.prelude.List.cons");
    let mut current = list_tid;
    loop {
        match kb.get_term(current).clone() {
            Term::Fn { ref functor, ref named_args, .. } => {
                if *functor == nil_sym {
                    break;
                }
                if *functor == cons_sym {
                    let head_tid = named_args.iter()
                        .find(|(s, _)| *s == head_sym)
                        .map(|(_, t)| *t);
                    let tail_tid = named_args.iter()
                        .find(|(s, _)| *s == tail_sym)
                        .map(|(_, t)| *t);

                    if let Some(h) = head_tid {
                        if let Term::Ref(sym) = kb.get_term(h) {
                            out.push((*sym, h));
                        }
                    }

                    match tail_tid {
                        Some(t) => current = t,
                        None => break,
                    }
                } else {
                    break;
                }
            }
            _ => break,
        }
    }
}

/// For each SortRequiresInfo fact with a SortView spec, complete the
/// instantiation by merging explicit bindings with auto-bound operations.
fn resolve_requires_bindings(kb: &mut KnowledgeBase) {
    let requires_sym = match kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo") {
        Some(sym) => sym,
        None => return,
    };
    let param_type_sym = match kb.try_resolve_symbol("anthill.reflect.SortView") {
        Some(sym) => sym,
        None => return,
    };

    let sort_ref_field = kb.intern("sort_ref");
    let spec_field = kb.intern("spec");

    let rule_ids = kb.rules_by_functor(requires_sym);

    // Collect facts to update: (rule_id, sort_ref_term, spec_sort_sym, explicit_named_args)
    let mut updates: Vec<(super::RuleId, TermId, Symbol, SmallVec<[(Symbol, TermId); 2]>)> = Vec::new();

    for rid in &rule_ids {
        if kb.is_requires_resolved(*rid) {
            continue;
        }
        if !kb.is_fact(*rid) {
            continue;
        }
        // Term-only binding completion (auto-bind ops, fill defaults). A
        // value-fact SortRequiresInfo (denoted-bearing spec — e.g. a `Modify[c]`
        // effect-row binding) carries its bindings explicitly and faithfully on
        // the occurrence; occurrence-based completion is the gated effect-
        // expressions-as-types work, so leave the fact as-is rather than hit the
        // term-only `rule_head` panic.
        let Some(named_args) = kb.fact_head_named_args(*rid) else { continue };
        let sort_ref_tid = named_args.iter()
            .find(|(s, _)| *s == sort_ref_field)
            .map(|(_, t)| *t);
        let spec_tid = named_args.iter()
            .find(|(s, _)| *s == spec_field)
            .map(|(_, t)| *t);

        if let (Some(sr_tid), Some(si_tid)) = (sort_ref_tid, spec_tid) {
            let si_term = kb.get_term(si_tid).clone();
            if let Term::Fn { functor, pos_args, named_args: inst_named, .. } = si_term {
                if functor == param_type_sym && !pos_args.is_empty() {
                    // Extract spec sort symbol from first pos_arg
                    let spec_sym = match kb.get_term(pos_args[0]) {
                        Term::Fn { functor: f, .. } => Some(*f),
                        Term::Ref(s) => Some(*s),
                        _ => None,
                    };

                    if let Some(ss) = spec_sym {
                        // WI-359: capture positional bindings too. `requires
                        // Ring[F]` stores `pos_args = [Ring-base, <F>]` with
                        // no named args; map each positional (after the base)
                        // to the spec's param in declaration order so it
                        // reaches the slot-fill loop below as a named binding
                        // — otherwise the slot falls back to the self-ref
                        // default and the cross-param link is lost.
                        let mut bindings = inst_named.clone();
                        if pos_args.len() > 1 {
                            let params = kb.type_params_of_sort(ss);
                            let named_shorts: Vec<String> = bindings.iter()
                                .map(|(k, _)| kb.resolve_sym(*k)
                                    .rsplit('.').next().unwrap_or("").to_string())
                                .collect();
                            for (i, pv) in pos_args.iter().skip(1).enumerate() {
                                if let Some(pname) = params.get(i) {
                                    if !named_shorts.iter().any(|s| s == pname) {
                                        let key = kb.intern(pname);
                                        bindings.push((key, *pv));
                                    }
                                }
                            }
                        }
                        updates.push((*rid, sr_tid, ss, bindings));
                    }
                }
            }
        }
    }

    // Now process each update
    for (rid, sort_ref_tid, spec_sort_sym, explicit_bindings) in updates {
        let base_subst = match kb.sort_base_subst(spec_sort_sym) {
            Some(bs) => bs.to_vec(),
            None => continue,
        };

        // Build complete bindings: start from base, override with explicit
        let mut complete: Vec<(Symbol, TermId)> = Vec::new();

        // Collect operation short names from the spec's SortInfo for auto-binding
        let op_syms = collect_sort_operations(kb, spec_sort_sym);
        let op_short_names: Vec<String> = op_syms.iter()
            .map(|s| {
                let name = kb.resolve_sym(*s);
                name.rsplit('.').next().unwrap_or(name).to_owned()
            })
            .collect();

        // Build a short-name lookup for explicit bindings.
        // Explicit bindings may use plain symbols (e.g., "T") while base_subst
        // uses scope-qualified symbols (e.g., "Monoid.T"). Match by short name.
        let explicit_by_short: Vec<(String, TermId)> = explicit_bindings.iter()
            .map(|(s, t)| {
                let name = kb.resolve_sym(*s);
                let short = name.rsplit('.').next().unwrap_or(name).to_owned();
                (short, *t)
            })
            .collect();

        for (slot_sym, default_tid) in &base_subst {
            let slot_name = kb.resolve_sym(*slot_sym);
            let slot_short = slot_name.rsplit('.').next().unwrap_or(slot_name).to_owned();

            // Check if explicit binding overrides this slot (by short name)
            let explicit_val = explicit_by_short.iter()
                .find(|(name, _)| *name == slot_short)
                .map(|(_, t)| *t);

            if let Some(val) = explicit_val {
                complete.push((*slot_sym, val));
            } else if op_short_names.contains(&slot_short) {
                // Auto-bind: look for same-named operation in the requiring sort's scope
                let auto_bound = find_operation_in_scope(kb, sort_ref_tid, &slot_short);
                match auto_bound {
                    Some(bound_sym) => {
                        let ref_term = kb.alloc(Term::Ref(bound_sym));
                        complete.push((*slot_sym, ref_term));
                    }
                    None => {
                        complete.push((*slot_sym, *default_tid));
                    }
                }
            } else {
                complete.push((*slot_sym, *default_tid));
            }
        }

        // Now build a new SortView term with complete bindings
        let old_head = kb.rule_head(rid);
        let old_head_term = kb.get_term(old_head).clone();
        if let Term::Fn { ref named_args, .. } = old_head_term {
            let old_spec_tid = named_args.iter()
                .find(|(s, _)| *s == spec_field)
                .map(|(_, t)| *t)
                .unwrap();

            let old_inst = kb.get_term(old_spec_tid).clone();
            if let Term::Fn { pos_args, .. } = old_inst {
                let new_named: SmallVec<[(Symbol, TermId); 2]> = complete.into_iter().collect();
                let new_inst = kb.alloc(Term::Fn {
                    functor: param_type_sym,
                    pos_args: pos_args.clone(),
                    named_args: new_named,
                });

                // Build new SortRequiresInfo fact with updated spec
                let new_named_args: SmallVec<[(Symbol, TermId); 2]> = named_args.iter()
                    .map(|(s, t)| {
                        if *s == spec_field {
                            (*s, new_inst)
                        } else {
                            (*s, *t)
                        }
                    })
                    .collect();
                let new_head = kb.alloc(Term::Fn {
                    functor: requires_sym,
                    pos_args: SmallVec::new(),
                    named_args: new_named_args,
                });

                // Retract old, assert new
                let sort = kb.rule_sort(rid);
                let domain = kb.rule_domain(rid);
                let meta = kb.rule_meta(rid);
                kb.retract(rid);
                let new_rid = kb.assert_fact(new_head, sort, domain, meta);
                kb.mark_requires_resolved(new_rid);
            }
        }
    }
}

/// Proposal 030 phase α.6: emit a synthetic `ProofRecord` fact for
/// every `requires <SE>` clause in a sort or operation declaration.
/// The witness is `ScopeAxiom(scope_kind, scope_qn, aspect)` —
/// definitionally checkable by re-reading the source declaration.
///
/// Naming: `<scope-qn>.requires.<SE-flat>` where `<SE-flat>` is the
/// spec's base sort short-name plus binding-value short-names sorted
/// by binding key. So `requires Eq[T]` inside `algebra.A` becomes
/// `algebra.A.requires.Eq_T`; `requires Monoid[T = Int64]` becomes
/// `<scope>.requires.Monoid_Int`.
///
/// Records land with `result = Pending` for now — phase β's witness
/// checker transitions them to `Discharged` once the structural
/// dispatch on `aspect` confirms the cited declaration is present.
/// State hash is the sentinel `"scope-axiom"` since these records
/// have no SLD/SMT dep slice; staleness is detected by re-reading
/// the declaration directly during β.4 checking.
///
/// Idempotent: if a ProofRecord with the same `rule` field already
/// exists in the KB (e.g. a previous load_phase already registered
/// it), the auto-registration is skipped to avoid duplicate facts.
fn register_requires_axiom_witnesses(kb: &mut KnowledgeBase) {
    let requires_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo") {
        Some(s) => s,
        None => return,
    };
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return,
    };
    let pending_sym = match kb.try_resolve_symbol(
        "anthill.realization.ObligationStatus.Pending"
    ) {
        Some(s) => s,
        None => return,
    };
    let strategy_open_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofStrategyOpen"
    ) {
        Some(s) => s,
        None => return,
    };
    let body_none_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofBodyNone"
    ) {
        Some(s) => s,
        None => return,
    };
    let scope_axiom_sym = match kb.try_resolve_symbol(
        "anthill.realization.witness.ProofWitness.ScopeAxiom"
    ) {
        Some(s) => s,
        None => return,
    };
    let nil_sym = match kb.try_resolve_symbol("anthill.prelude.List.nil") {
        Some(s) => s,
        None => return,
    };

    let sort_ref_field = kb.intern("sort_ref");
    let spec_field = kb.intern("spec");
    let rule_arg = kb.intern("rule");
    let strategy_arg = kb.intern("strategy");
    let body_arg = kb.intern("body");
    let result_arg = kb.intern("result");
    let deps_arg = kb.intern("dependencies");
    let using_arg = kb.intern("using");
    let witness_arg = kb.intern("witness");
    let state_hash_arg = kb.intern("state_hash");
    let parametric_context_arg = kb.intern("parametric_context");
    let scope_kind_arg = kb.intern("scope_kind");
    let scope_qn_arg = kb.intern("scope_qn");
    let aspect_arg = kb.intern("aspect");

    let existing_rule_qns = collect_existing_proof_record_qns(kb, record_sym);
    let requires_rids = kb.rules_by_functor(requires_info_sym);
    let mut new_records: Vec<TermId> = Vec::new();

    for rid in requires_rids {
        if !kb.is_fact(rid) { continue; }
        // Term-only scope-axiom generation. A value-fact SortRequiresInfo
        // (denoted-bearing spec) is carried faithfully; occurrence-based axiom
        // generation is gated effect-expressions-as-types work, so skip rather
        // than hit the term-only `rule_head` panic.
        let Some(named) = kb.fact_head_named_args(rid) else { continue };

        let sort_ref_tid = match named.iter()
            .find(|(s, _)| *s == sort_ref_field).map(|(_, t)| *t) {
            Some(t) => t,
            None => continue,
        };
        let spec_tid = match named.iter()
            .find(|(s, _)| *s == spec_field).map(|(_, t)| *t) {
            Some(t) => t,
            None => continue,
        };

        let scope_qn = match qn_of_sort_ref(kb, sort_ref_tid) {
            Some(q) => q,
            None => continue,
        };
        let se_flat = match flatten_spec(kb, spec_tid) {
            Some(s) => s,
            None => continue,
        };
        let aspect_text = format!("requires.{se_flat}");
        let rule_qn_text = format!("{scope_qn}.{aspect_text}");
        if existing_rule_qns.contains(&rule_qn_text) { continue; }

        let scope_kind_term = kb.alloc(Term::Const(Literal::String("sort".to_string())));
        let scope_qn_term = kb.alloc(Term::Const(Literal::String(scope_qn.clone())));
        let aspect_term = kb.alloc(Term::Const(Literal::String(aspect_text)));
        let witness_term = kb.alloc(Term::Fn {
            functor: scope_axiom_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (scope_kind_arg, scope_kind_term),
                (scope_qn_arg, scope_qn_term),
                (aspect_arg, aspect_term),
            ]),
        });
        let strategy_term = kb.alloc(Term::Fn {
            functor: strategy_open_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let body_term = kb.alloc(Term::Fn {
            functor: body_none_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let pending_term = kb.alloc(Term::Fn {
            functor: pending_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let nil_term = kb.alloc(Term::Fn {
            functor: nil_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let rule_text_term = kb.alloc(Term::Const(Literal::String(rule_qn_text)));
        let state_hash_term = kb.alloc(Term::Const(
            Literal::String("scope-axiom".to_string())
        ));

        let record_term = kb.alloc(Term::Fn {
            functor: record_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (rule_arg, rule_text_term),
                (strategy_arg, strategy_term),
                (body_arg, body_term),
                (result_arg, pending_term),
                (deps_arg, nil_term),
                (using_arg, nil_term),
                (witness_arg, witness_term),
                (state_hash_arg, state_hash_term),
                (parametric_context_arg, nil_term),
            ]),
        });
        new_records.push(record_term);
    }

    if new_records.is_empty() { return; }
    let record_sort_term = kb.make_name_term("anthill.realization.ProofRecord");
    let global_term = kb.make_name_term("_global");
    for rec in new_records {
        kb.assert_metadata_fact(rec, record_sort_term, global_term, None);
    }
}

/// Proposal 030 phase α.7: emit a synthetic `ProofRecord` fact for
/// every inductive sort's induction principle. Witness shape mirrors
/// α.6's `requires` clauses but with `aspect = "induction"`.
///
/// v0 scope: enum sorts (`SortInfo.kind = "enum"`) get an induction
/// ProofRecord. Non-enum sorts with recursive constructors are
/// deferred — recursion detection requires walking EntityInfo and
/// matching constructor field types against the parent sort, which
/// is straightforward but additional code; recursive ADTs picked up
/// in a follow-up sub-task. Primitives with hand-written `induction`
/// rules in stdlib (Int64.induction, BigInt.induction, …) are *not*
/// re-registered here — those rules already exist as user-visible
/// anthill rules and phase γ resolves citations against them
/// directly. The auto-registered records here cover the kernel-
/// derived structural induction for user-declared inductive sorts.
///
/// The witness is `ScopeAxiom(scope_kind: "sort", scope_qn: <T>,
/// aspect: "induction")`. Phase β.4's check re-reads T's SortInfo
/// and confirms the constructor list matches what the principle was
/// derived from.
///
/// Idempotent across loads via the same `existing_rule_qns` guard
/// as α.6.
fn register_induction_axiom_witnesses(kb: &mut KnowledgeBase) {
    let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        Some(s) => s,
        None => return,
    };
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return,
    };
    let pending_sym = match kb.try_resolve_symbol(
        "anthill.realization.ObligationStatus.Pending"
    ) { Some(s) => s, None => return };
    let strategy_open_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofStrategyOpen"
    ) { Some(s) => s, None => return };
    let body_none_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofBodyNone"
    ) { Some(s) => s, None => return };
    let scope_axiom_sym = match kb.try_resolve_symbol(
        "anthill.realization.witness.ProofWitness.ScopeAxiom"
    ) { Some(s) => s, None => return };
    let nil_sym = match kb.try_resolve_symbol("anthill.prelude.List.nil") {
        Some(s) => s, None => return,
    };

    let rule_arg = kb.intern("rule");
    let strategy_arg = kb.intern("strategy");
    let body_arg = kb.intern("body");
    let result_arg = kb.intern("result");
    let deps_arg = kb.intern("dependencies");
    let using_arg = kb.intern("using");
    let witness_arg = kb.intern("witness");
    let state_hash_arg = kb.intern("state_hash");
    let parametric_context_arg = kb.intern("parametric_context");
    let scope_kind_arg = kb.intern("scope_kind");
    let scope_qn_arg = kb.intern("scope_qn");
    let aspect_arg = kb.intern("aspect");

    let existing_rule_qns = collect_existing_proof_record_qns(kb, record_sym);
    let sort_info_rids = kb.rules_by_functor(sort_info_sym);
    let mut new_records: Vec<TermId> = Vec::new();

    for rid in sort_info_rids {
        if !kb.is_fact(rid) { continue; }
        let Some(head) = kb.fact_head_term(rid) else { continue };
        let head_term = kb.get_term(head).clone();
        let named = match head_term {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };

        if !sort_info_is_inductive(kb, &named) { continue; }
        let sort_qn = match sort_info_qn(kb, &named) {
            Some(q) => q,
            None => continue,
        };
        let rule_qn_text = format!("{sort_qn}.induction");
        if existing_rule_qns.contains(&rule_qn_text) { continue; }

        let scope_kind_term = kb.alloc(Term::Const(Literal::String("sort".to_string())));
        let scope_qn_term = kb.alloc(Term::Const(Literal::String(sort_qn)));
        let aspect_term = kb.alloc(Term::Const(Literal::String("induction".to_string())));
        let witness_term = kb.alloc(Term::Fn {
            functor: scope_axiom_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (scope_kind_arg, scope_kind_term),
                (scope_qn_arg, scope_qn_term),
                (aspect_arg, aspect_term),
            ]),
        });
        let strategy_term = kb.alloc(Term::Fn {
            functor: strategy_open_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let body_term = kb.alloc(Term::Fn {
            functor: body_none_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let pending_term = kb.alloc(Term::Fn {
            functor: pending_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let nil_term = kb.alloc(Term::Fn {
            functor: nil_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let rule_text_term = kb.alloc(Term::Const(Literal::String(rule_qn_text)));
        let state_hash_term = kb.alloc(Term::Const(
            Literal::String("scope-axiom".to_string())
        ));

        let record_term = kb.alloc(Term::Fn {
            functor: record_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (rule_arg, rule_text_term),
                (strategy_arg, strategy_term),
                (body_arg, body_term),
                (result_arg, pending_term),
                (deps_arg, nil_term),
                (using_arg, nil_term),
                (witness_arg, witness_term),
                (state_hash_arg, state_hash_term),
                (parametric_context_arg, nil_term),
            ]),
        });
        new_records.push(record_term);
    }

    if new_records.is_empty() { return; }
    let record_sort_term = kb.make_name_term("anthill.realization.ProofRecord");
    let global_term = kb.make_name_term("_global");
    for rec in new_records {
        kb.assert_metadata_fact(rec, record_sort_term, global_term, None);
    }
}

/// Proposal 030 phase α.8 / WI-119 Variant 3 / WI-120 — emit
/// `Specialization`-witnessed ProofRecords for each `provides A[T =
/// X]` clause whose required laws all have Discharged ProofRecords
/// at the substitution.
///
/// Algorithm: walk `SortProvidesInfo` facts. For each `(X, A[T = X])`:
///   1. Resolve A's qualified name and the substitution σ from the
///      spec view's named bindings (filtering operation auto-bindings).
///   2. For each of A's auto-registered `<A-qn>.requires.<SE>`
///      ProofRecords (α.6), emit a `Specialization` ProofRecord
///      named `<X-qn>.provides.<A-flat>.<SE>` whose witness is
///      `Specialization { parametric: <A-qn>.requires.<SE>,
///      substitution: σ, instances: [] }`. The instances list is
///      empty in v0 — phase β.5's structural check verifies
///      coverage by walking the existing registry rather than
///      chasing a pre-baked instance-list. Future refinement: pre-
///      compute the per-law instance ProofRecord QNs and embed.
///   3. Phase β.5's check enforces: for each requires-law `<SE>`,
///      either an instance ProofRecord covers it at σ, or a
///      ScopeAxiom on X's own declaration does. Errors at check
///      time, not load time — so missing proofs surface in
///      `anthill check`'s integrity audit, not as load failures.
///
/// Idempotent across loads via `existing_rule_qns`.
fn register_specialization_witnesses(kb: &mut KnowledgeBase) {
    let provides_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") {
        Some(s) => s,
        None => return,
    };
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return,
    };
    let pending_sym = match kb.try_resolve_symbol(
        "anthill.realization.ObligationStatus.Pending"
    ) { Some(s) => s, None => return };
    let strategy_open_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofStrategyOpen"
    ) { Some(s) => s, None => return };
    let body_none_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofBodyNone"
    ) { Some(s) => s, None => return };
    let specialization_sym = match kb.try_resolve_symbol(
        "anthill.realization.witness.ProofWitness.Specialization"
    ) { Some(s) => s, None => return };
    let sort_binding_sym = match kb.try_resolve_symbol(
        "anthill.realization.witness.SortBinding"
    ) { Some(s) => s, None => return };
    let nil_sym = match kb.try_resolve_symbol("anthill.prelude.List.nil") {
        Some(s) => s, None => return,
    };
    let cons_sym = match kb.try_resolve_symbol("anthill.prelude.List.cons") {
        Some(s) => s, None => return,
    };

    let rule_arg = kb.intern("rule");
    let strategy_arg = kb.intern("strategy");
    let body_arg = kb.intern("body");
    let result_arg = kb.intern("result");
    let deps_arg = kb.intern("dependencies");
    let using_arg = kb.intern("using");
    let witness_arg = kb.intern("witness");
    let state_hash_arg = kb.intern("state_hash");
    let parametric_context_arg = kb.intern("parametric_context");
    let head_arg = kb.intern("head");
    let tail_arg = kb.intern("tail");
    let parametric_arg = kb.intern("parametric");
    let substitution_arg = kb.intern("substitution");
    let instances_arg = kb.intern("instances");
    let abstract_param_arg = kb.intern("abstract_param");
    let concrete_sort_arg = kb.intern("concrete_sort");

    let existing_rule_qns = collect_existing_proof_record_qns(kb, record_sym);

    // Snapshot all (X-qn, spec-tid) pairs first so we don't borrow-
    // conflict with kb mutations during ProofRecord construction.
    let provides_rids = kb.rules_by_functor(provides_info_sym);
    let mut targets: Vec<(String, TermId)> = Vec::new();
    for rid in provides_rids {
        if !kb.is_fact(rid) { continue; }
        // Term-only specialization-proof emission. A value-fact SortProvidesInfo
        // (denoted-bearing spec) is carried faithfully; occurrence-based proof
        // emission is gated effect-expressions-as-types work, so skip rather than
        // hit the term-only `rule_head` panic on a value head.
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let sort_ref_tid = match super::typing::get_named_arg(kb, &named, "sort_ref") {
            Some(t) => t,
            None => continue,
        };
        let spec_tid = match super::typing::get_named_arg(kb, &named, "spec") {
            Some(t) => t,
            None => continue,
        };
        let x_qn = match qn_of_sort_ref(kb, sort_ref_tid) {
            Some(q) => q,
            None => continue,
        };
        targets.push((x_qn, spec_tid));
    }

    let mut new_records: Vec<TermId> = Vec::new();

    for (x_qn, spec_tid) in targets {
        let (a_short, a_qn, substitution) = match resolve_provides_spec(kb, spec_tid) {
            Some(t) => t,
            None => continue,
        };
        // Find every auto-registered <a_qn>.requires.<SE> record so
        // we can emit one Specialization per requires-law.
        let parametric_records: Vec<String> = existing_rule_qns
            .iter()
            .filter(|qn| qn.starts_with(&format!("{a_qn}.requires.")))
            .cloned()
            .collect();
        if parametric_records.is_empty() { continue; }

        for parametric_qn in parametric_records {
            let se_part = parametric_qn
                .strip_prefix(&format!("{a_qn}.requires."))
                .unwrap_or(&parametric_qn);
            let rule_qn_text = format!("{x_qn}.provides.{a_short}.{se_part}");
            if existing_rule_qns.contains(&rule_qn_text) { continue; }

            let parametric_term = kb.alloc(Term::Const(
                Literal::String(parametric_qn.clone())
            ));
            // Build the substitution cons-list of SortBinding entities.
            let binding_terms: Vec<TermId> = substitution.iter().map(|(k, v)| {
                let k_term = kb.alloc(Term::Const(Literal::String(k.clone())));
                let v_term = kb.alloc(Term::Const(Literal::String(v.clone())));
                kb.alloc(Term::Fn {
                    functor: sort_binding_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (abstract_param_arg, k_term),
                        (concrete_sort_arg, v_term),
                    ]),
                })
            }).collect();
            let substitution_list = build_cons_list(
                kb, &binding_terms, nil_sym, cons_sym, head_arg, tail_arg);
            let instances_list = kb.alloc(Term::Fn {
                functor: nil_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });

            let witness_term = kb.alloc(Term::Fn {
                functor: specialization_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[
                    (parametric_arg, parametric_term),
                    (substitution_arg, substitution_list),
                    (instances_arg, instances_list),
                ]),
            });
            let strategy_term = kb.alloc(Term::Fn {
                functor: strategy_open_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            let body_term = kb.alloc(Term::Fn {
                functor: body_none_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            let pending_term = kb.alloc(Term::Fn {
                functor: pending_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            let nil_term = kb.alloc(Term::Fn {
                functor: nil_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            let rule_text_term = kb.alloc(Term::Const(Literal::String(rule_qn_text)));
            let state_hash_term = kb.alloc(Term::Const(
                Literal::String("specialization".to_string())
            ));

            let record_term = kb.alloc(Term::Fn {
                functor: record_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[
                    (rule_arg, rule_text_term),
                    (strategy_arg, strategy_term),
                    (body_arg, body_term),
                    (result_arg, pending_term),
                    (deps_arg, nil_term),
                    (using_arg, nil_term),
                    (witness_arg, witness_term),
                    (state_hash_arg, state_hash_term),
                    (parametric_context_arg, nil_term),
                ]),
            });
            new_records.push(record_term);
        }
    }

    if new_records.is_empty() { return; }
    let record_sort_term = kb.make_name_term("anthill.realization.ProofRecord");
    let global_term = kb.make_name_term("_global");
    for rec in new_records {
        kb.assert_metadata_fact(rec, record_sort_term, global_term, None);
    }
}

/// WI-240 — build the per-sort operations table: each sort symbol
/// carries a `op_short → impl_op_symbol` map of the operations it can
/// dispatch (docs/design/operation-call-model.md §"Sort symbols carry
/// their own operations table").
///
/// Two passes:
///   1. **Own ops.** For every sort `S`, record `S.<op> → S.<op>` for
///      each op `S` itself declares. A direct/concrete impl thus
///      resolves its own ops without any spec involvement.
///   2. **Inherited spec ops.** For every impl sort `S` with a
///      `fact Spec[bindings]`, walk `Spec`'s declared operations. For
///      each op `S` does *not* declare itself (pass 1 already recorded
///      the ones it does), record the spec op `Spec.<op>` — its body
///      comes from the spec's rewrite rule or a registered builtin,
///      resolved at runtime. This mirrors the old dispatch fallback
///      (`impl.<op>` if the impl declares it, else `spec.<op>`); the
///      separate decision of whether to *rewrite* a spec-op call to a
///      runnable impl op stays in the typer (`op_has_runnable_body`).
///
/// This precomputes (once, at load time) the decision the dispatch
/// fallback used to make per-call via
/// `try_resolve_symbol("{impl_qn}.{op}").or_else(spec_qn)`. Consumers
/// read it via `kb.sort_ops_lookup(impl_sort, op_short)` — a direct
/// table lookup. Idempotent: re-running overwrites with equal values.
pub fn build_sort_ops_table(kb: &mut KnowledgeBase) {
    // One `SortInfo` scan shared by both passes: pass 1 records each
    // sort's own ops, pass 2 reads the spec sort's ops from the same
    // map. Scanning per sort via `operations_of_sort` would be
    // O(sorts²). Snapshot before inserting: interning short names
    // mutates `kb`, which can't overlap the `rules_by_functor` walk.
    let sort_ops: HashMap<Symbol, Vec<Symbol>> = sorts_and_own_ops(kb).into_iter().collect();

    // ── Pass 1: every sort's own declared operations. ──────────────
    for (sort_sym, ops) in &sort_ops {
        for &op_sym in ops {
            let short_sym = intern_op_short(kb, op_sym);
            kb.insert_sort_op(*sort_sym, short_sym, op_sym);
        }
    }

    // ── Pass 2: inherited spec ops for `fact Spec[bindings]` impls. ─
    let provides_sym = match kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") {
        Some(s) => s,
        None => return,
    };
    // Snapshot (impl_sort, spec_sort) pairs first — populating the
    // table interns short names (mutating `kb`), which can't overlap
    // the `rules_by_functor` borrow walk.
    let mut pairs: Vec<(Symbol, Symbol)> = Vec::new();
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) { continue; }
        // A value-fact SortProvidesInfo (denoted-bearing spec) is carried
        // faithfully; occurrence-based op-table inheritance is gated effect-
        // expressions-as-types work, so skip rather than hit the term-only
        // `rule_head` panic on a value head.
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let sort_ref_tid = match super::typing::get_named_arg(kb, &named, "sort_ref") {
            Some(t) => t,
            None => continue,
        };
        let spec_tid = match super::typing::get_named_arg(kb, &named, "spec") {
            Some(t) => t,
            None => continue,
        };
        let impl_sym = match sort_ref_functor(kb, sort_ref_tid) {
            Some(s) => s,
            None => continue,
        };
        let spec_sym = match provides_spec_base_sym(kb, spec_tid) {
            Some(s) => s,
            None => continue,
        };
        pairs.push((impl_sym, spec_sym));
    }

    for (impl_sym, spec_sym) in pairs {
        let Some(spec_ops) = sort_ops.get(&spec_sym) else { continue };
        for &spec_op_sym in spec_ops {
            let short_sym = intern_op_short(kb, spec_op_sym);
            // Pass 1 already recorded the impl's own override (if it
            // declares this op). Only fill the inherited spec default
            // when the impl doesn't declare the op itself.
            if kb.sort_ops_lookup(impl_sym, short_sym).is_none() {
                kb.insert_sort_op(impl_sym, short_sym, spec_op_sym);
            }
        }
    }

    // ── Pass 3 (WI-616): the semantic-equality dispatch index. ─────
    // For every sort whose sort_ops row carries a GENUINE own `eq` member
    // (`carrier_own_op`: not the `PartialEq.eq` spec op, parented by the sort
    // itself — never a pass-2-inherited foreign same-short-name default), key that
    // target under the shapes the sort's VALUES are headed by: its entity
    // constructors and its SELF-RETURNING ops (`Set.insert`/`Set.empty`;
    // `Map.get` returns an Option, not a Map, and must not key Map dispatch).
    // The resolver's `eq`/`neq` builtin probes this per structurally-unequal
    // goal — precomputing here keeps that path to one hash lookup.
    // WI-644: the semantic eq op moved from `Eq` to its base `PartialEq`.
    // WI-625 gap 2: a carrier with NO own `eq` but a RETROACTIVE instance fact
    // (`fact PartialEq[T = X, eq = myEq]`) keys to the bound op `myEq` instead —
    // so the resolver/eval `eq` dispatches through it rather than answering
    // structurally (`myEq` is typically bodied ⇒ dispatched via the eval bridge).
    let Some(eq_spec) = kb.try_resolve_symbol("anthill.prelude.PartialEq.eq") else { return };
    let eq_short = kb.intern("eq");
    let partialeq_sort = kb.try_resolve_symbol("anthill.prelude.PartialEq");
    let eq_sort = kb.try_resolve_symbol("anthill.prelude.Eq");
    let mut entries: Vec<(Symbol, Symbol)> = Vec::new();
    for &sort_sym in sort_ops.keys() {
        // Carrier's own `eq` wins (a genuine override); else a retroactive
        // instance fact's bound `eq` op. `None` ⇒ no eq override for this sort.
        let target = super::typing::carrier_own_op(kb, sort_sym, eq_spec, eq_short)
            .or_else(|| instance_fact_eq_target(kb, sort_sym, partialeq_sort, eq_sort));
        let Some(target) = target else {
            continue;
        };
        for ctor in kb.constructors_of_sort(sort_sym) {
            entries.push((ctor, target));
        }
        let sort_canon = kb.canonical_sort_sym(sort_sym);
        for &op_sym in sort_ops.get(&sort_sym).into_iter().flatten() {
            // No OperationInfo ⇒ not a classifiable value shape (e.g. the
            // auto-bound short-name ops a `provides` block registers) — such a
            // symbol never heads a constructed value, so skipping it cannot
            // hide a dispatchable shape.
            let Some(rec) = super::op_info::lookup_operation_info(kb, op_sym) else { continue };
            let self_returning = super::typing::sort_functor_of_view(kb, &rec.return_type)
                .map(|h| kb.canonical_sort_sym(h) == sort_canon)
                .unwrap_or(false);
            if self_returning {
                entries.push((op_sym, target));
            }
        }
    }
    // Key each entry under BOTH the raw symbol and its canonical copy: the
    // probe side (`eq_dispatch_target`) reads a goal-head functor raw (O(1),
    // no per-probe canonicalization), and one qualified name can be interned
    // under several Symbols.
    for (functor, target) in entries {
        let canon = kb.canonical_sym(functor);
        kb.insert_eq_dispatch(functor, target);
        if canon != functor {
            kb.insert_eq_dispatch(canon, target);
        }
    }
}

/// WI-625 gap 2 — the operation a RETROACTIVE instance fact binds to `eq` for
/// `carrier` (`fact PartialEq[T = carrier, eq = myEq]` ⇒ `myEq`), or `None`. The
/// eq-dispatch fallback when `carrier` owns no `eq` member of its own: an instance
/// fact supplies `eq` OFF-carrier (as a free-standing op), so the index must key
/// the carrier's values to the bound op — otherwise the resolver/eval `eq`
/// answers structurally, diverging from `List.member` (which honors the fact via
/// the threaded dict). Checks the `PartialEq` fact (where `eq` canonically lives
/// post-WI-644), then the `Eq` fact (a user who wrote only `fact Eq[…, eq = …]`).
fn instance_fact_eq_target(
    kb: &KnowledgeBase,
    carrier: Symbol,
    partialeq_sort: Option<Symbol>,
    eq_sort: Option<Symbol>,
) -> Option<Symbol> {
    partialeq_sort
        .and_then(|s| super::typing::instance_fact_op_binding(kb, carrier, s, "eq"))
        .or_else(|| {
            eq_sort.and_then(|s| super::typing::instance_fact_op_binding(kb, carrier, s, "eq"))
        })
}

/// Intern the short name of an operation symbol (`Spec.lt` → `lt`) —
/// the `sort_ops` inner key. Borrows the QN, slices, then interns the
/// slice (no intermediate `String`).
fn intern_op_short(kb: &mut KnowledgeBase, op_sym: Symbol) -> Symbol {
    let short = last_segment(kb.qualified_name_of(op_sym)).to_string();
    kb.intern(&short)
}

/// Walk `SortInfo` facts once, returning each sort symbol paired with
/// the operation symbols it declares. `build_sort_ops_table` collects
/// this into a map both passes share — a single scan instead of one
/// `SortInfo` walk per sort.
pub(crate) fn sorts_and_own_ops(kb: &KnowledgeBase) -> Vec<(Symbol, Vec<Symbol>)> {
    let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        Some(s) => s,
        None => return Vec::new(),
    };
    let mut out: Vec<(Symbol, Vec<Symbol>)> = Vec::new();
    for rid in kb.rules_by_functor(sort_info_sym) {
        if !kb.is_fact(rid) { continue; }
        let Some(head) = kb.fact_head_term(rid) else { continue };
        let named = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };
        let sort_sym = match named.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "name")
            .map(|(_, v)| *v)
            .map(|t| kb.get_term(t))
        {
            Some(Term::Ref(s) | Term::Ident(s) | Term::Fn { functor: s, .. }) => *s,
            _ => continue,
        };
        let ops = match named.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "operations")
            .map(|(_, v)| *v)
        {
            Some(ops_tid) => super::typing::list_to_vec(kb, ops_tid)
                .into_iter()
                .filter_map(|t| match kb.get_term(t) {
                    Term::Ref(s) => Some(*s),
                    _ => None,
                })
                .collect(),
            None => Vec::new(),
        };
        out.push((sort_sym, ops));
    }
    out
}

/// The set of sorts that have at least one constructor (`SortInfo.constructors`
/// is non-empty) — i.e. *concrete* sorts that can be instantiated, as opposed to
/// *abstract* spec/parametric sorts whose ops may stay primitives. WI-363 uses
/// this to scope op-provision completeness to concrete carriers: an abstract
/// carrier declaring `fact Spec[Self]` (e.g. `LogicalStream`, whose `splitFirst`
/// is a body-less primitive) is a sub-interface, not a runtime witness, so its
/// ops needn't resolve — the obligation passes to its concrete sub-carriers.
pub(crate) fn sorts_with_constructors(kb: &KnowledgeBase) -> std::collections::HashSet<Symbol> {
    let mut out = std::collections::HashSet::new();
    let Some(sort_info_sym) = kb.try_resolve_symbol("anthill.reflect.SortInfo") else {
        return out;
    };
    for rid in kb.rules_by_functor(sort_info_sym) {
        if !kb.is_fact(rid) { continue; }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let sort_sym = match named.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "name")
            .map(|(_, v)| kb.get_term(*v))
        {
            Some(Term::Ref(s) | Term::Ident(s) | Term::Fn { functor: s, .. }) => *s,
            _ => continue,
        };
        let has_ctors = named.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "constructors")
            .map(|(_, v)| !super::typing::list_to_vec(kb, *v).is_empty())
            .unwrap_or(false);
        if has_ctors {
            out.insert(sort_sym);
        }
    }
    out
}

/// WI-346 — requires-shadow lint. A sort that `requires` a spec and declares a
/// local operation whose short name matches one of that spec's *own* operations
/// shadows the inherited name. Per `kernel-language.md` §8.7 those are distinct,
/// unrelated symbols — `requires` never overrides (override is the `provides`
/// direction; a value viewed as the spec projects the spec's op, not the local
/// one) — so it loads, but it is a frequent footgun: the author usually meant to
/// override. Emit a non-fatal [`LoadWarning::RequiresShadow`] naming the sort,
/// op, and spec.
///
/// A sort that also *provides* the spec (`fact Spec[sort]`) is skipped: there the
/// own op IS the override (own-op-beats-inherited), which is intentional. Only
/// the spec's *direct* own ops are compared (not transitively inherited ones) —
/// the common, on-the-nose case; transitive shadows can be a follow-up.
fn check_requires_shadows(kb: &mut KnowledgeBase) -> Vec<LoadWarning> {
    // Own declared ops per sort — an owned snapshot, so no immutable borrow of
    // `kb` is held across the `&mut`/`&` calls in the loop below.
    let own: HashMap<Symbol, Vec<Symbol>> =
        sorts_and_own_ops(kb).into_iter().collect();
    // Short name = last `.`-segment of the operation's qualified name
    // (`a.b.Sort.op` → `op`); robust regardless of how the symbol interns.
    let op_short = |kb: &KnowledgeBase, s: Symbol| -> String {
        kb.qualified_name_of(s).rsplit('.').next().unwrap_or("").to_string()
    };
    let mut warnings = Vec::new();
    for (&sort, ops) in &own {
        if ops.is_empty() { continue; }
        for entry in super::typing::direct_requires_chain(kb, sort) {
            let spec = entry.required_sort;
            // A provider's own op is a legitimate override, not a shadow.
            if super::typing::sort_provides(kb, sort, spec) { continue; }
            let Some(spec_ops) = own.get(&spec) else { continue };
            if spec_ops.is_empty() { continue; }
            let spec_short: std::collections::HashSet<String> =
                spec_ops.iter().map(|&s| op_short(kb, s)).collect();
            for &op in ops {
                let osn = op_short(kb, op);
                if spec_short.contains(&osn) {
                    warnings.push(LoadWarning::RequiresShadow {
                        sort: kb.qualified_name_of(sort).to_string(),
                        op: osn,
                        spec: kb.qualified_name_of(spec).to_string(),
                    });
                }
            }
        }
    }
    warnings
}

/// Extract the carrier sort symbol from a `SortProvidesInfo.sort_ref`
/// term — a `sort_ref(name: Ref(S))`, a bare `Ref(S)`/`Ident(S)`, or a
/// nullary `Fn` whose functor is `S`.
pub(crate) fn sort_ref_functor(kb: &KnowledgeBase, term: TermId) -> Option<Symbol> {
    match kb.get_term(term) {
        Term::Fn { functor, named_args, .. } => {
            // `sort_ref(name: Ref(S))` wrapping — prefer the inner name.
            if let Some(name_tid) = named_args.iter()
                .find(|(k, _)| kb.resolve_sym(*k) == "name")
                .map(|(_, v)| *v)
            {
                if let Term::Ref(s) | Term::Ident(s) = kb.get_term(name_tid) {
                    return Some(*s);
                }
            }
            Some(*functor)
        }
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// Extract the spec sort symbol from a `SortProvidesInfo.spec` term:
/// the base of a `SortView(Spec, …)` wrapper, or a bare spec ref.
pub(crate) fn provides_spec_base_sym(kb: &KnowledgeBase, spec: TermId) -> Option<Symbol> {
    match kb.get_term(spec) {
        Term::Fn { functor, pos_args, .. } => {
            let f_short = last_segment(kb.qualified_name_of(*functor));
            if f_short == "SortView" {
                let base = pos_args.first().copied()?;
                match kb.get_term(base) {
                    Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => {
                        Some(*functor)
                    }
                    _ => None,
                }
            } else {
                Some(*functor)
            }
        }
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// Resolve a SortProvidesInfo.spec term into:
/// - the spec's short name (used as `<A-flat>` in the rule QN)
/// - the spec's qualified name (used to find α.6's requires records)
/// - the substitution as `Vec<(abstract_param, concrete_sort_short)>`
fn resolve_provides_spec(
    kb: &KnowledgeBase,
    spec: TermId,
) -> Option<(String, String, Vec<(String, String)>)> {
    // Peel `SortView(Spec, …)` (or a bare spec ref) down to the base
    // spec symbol — same logic as `provides_spec_base_sym`.
    let base_sym = provides_spec_base_sym(kb, spec)?;
    let qn = kb.qualified_name_of(base_sym).to_owned();
    let short = last_segment(&qn).to_owned();
    // The type-parameter substitution lives in the outer `SortView`'s
    // named args; a plain `provides Foo` (non-SortView Fn or bare ref)
    // carries none.
    let sub = match kb.get_term(spec) {
        Term::Fn { functor, named_args, .. }
            if last_segment(kb.qualified_name_of(*functor)) == "SortView" =>
        {
            sort_view_substitution(kb, named_args)
        }
        _ => Vec::new(),
    };
    Some((short, qn, sub))
}

/// Parse a `SortView`'s named args into the type-parameter substitution
/// `Vec<(abstract_param_short, concrete_sort_short)>`, sorted by param.
/// Operation-valued args are skipped (they bind ops, not type params).
fn sort_view_substitution(
    kb: &KnowledgeBase,
    named_args: &[(Symbol, TermId)],
) -> Vec<(String, String)> {
    use crate::intern::SymbolKind;
    let mut sub: Vec<(String, String)> = named_args.iter().filter_map(|(k_sym, v_tid)| {
        // The base sort the binding names. WI-449: a parameterized binding value
        // rides a `SortView(base, …)` wrapper (`C = List[T]` → `SortView(List, …)`)
        // on BOTH the `provides` and the now-aligned `fact` path — `provides_spec_base_sym`
        // unwraps it to `List`, where a raw functor read would yield the literal
        // `SortView`. A bare op-valued binding stays its own functor, so the
        // operation skip below is unaffected.
        let value_sym = provides_spec_base_sym(kb, *v_tid);
        if let Some(vs) = value_sym {
            if matches!(kb.kind_of(vs), Some(SymbolKind::Operation)) {
                return None;
            }
        }
        let k_short = last_segment(kb.resolve_sym(*k_sym)).to_owned();
        let v_short = match value_sym {
            Some(s) => last_segment(kb.resolve_sym(s)).to_owned(),
            None => "_".to_string(),
        };
        Some((k_short, v_short))
    }).collect();
    sub.sort_by(|a, b| a.0.cmp(&b.0));
    sub
}

/// Build a cons/nil list using explicit functor symbols. Mirrors
/// `build_list` but accepts pre-resolved nil/cons/head/tail symbols
/// — useful when the caller already resolved them once and wants
/// to avoid re-lookups in inner loops.
pub(crate) fn build_cons_list(
    kb: &mut KnowledgeBase,
    items: &[TermId],
    nil_sym: Symbol,
    cons_sym: Symbol,
    head_arg: Symbol,
    tail_arg: Symbol,
) -> TermId {
    let mut list = kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    for &item in items.iter().rev() {
        list = kb.alloc(Term::Fn {
            functor: cons_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(head_arg, item), (tail_arg, list)]),
        });
    }
    list
}

/// True iff a SortInfo fact's `kind` field is `"enum"` — the v0
/// detection criterion for "needs an induction principle". The
/// loader emits `kind` as `Term::Ident(intern("enum"))` (see
/// `assert_sort_info`), so we look up the symbol's interned name.
/// Recursive ADTs (kind = "sort" with self-referential constructor
/// fields) are deferred; this function returns false for them today.
pub fn sort_info_is_inductive(
    kb: &KnowledgeBase,
    named: &SmallVec<[(Symbol, TermId); 2]>,
) -> bool {
    let kind_tid = match super::typing::get_named_arg(kb, named, "kind") {
        Some(t) => t,
        None => return false,
    };
    match kb.get_term(kind_tid) {
        Term::Ident(s) | Term::Ref(s) => kb.resolve_sym(*s) == "enum",
        Term::Const(Literal::String(s)) => s == "enum",
        _ => false,
    }
}

/// Resolve a SortInfo's `name` field to its qualified name. The
/// `name` field is a symbol reference (Term::Ref / Term::Ident /
/// nullary Fn), encoded by the loader as `<sort-qn>` in the
/// symbol table.
pub fn sort_info_qn(
    kb: &KnowledgeBase,
    named: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<String> {
    let tid = super::typing::get_named_arg(kb, named, "name")?;
    let sym = match kb.get_term(tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        Term::Fn { functor, .. } => *functor,
        _ => return None,
    };
    Some(kb.qualified_name_of(sym).to_owned())
}

/// Read the `rule` field of every existing `ProofRecord` fact so the
/// auto-registration in `register_requires_axiom_witnesses` can skip
/// duplicates.
fn collect_existing_proof_record_qns(kb: &KnowledgeBase, record_sym: Symbol) -> HashSet<String> {
    let mut out = HashSet::new();
    for rid in kb.rules_by_functor(record_sym) {
        if !kb.is_fact(rid) { continue; }
        let Some(head) = kb.fact_head_term(rid) else { continue };
        if let Term::Fn { named_args, .. } = kb.get_term(head) {
            if let Some(tid) = super::typing::get_named_arg(kb, named_args, "rule") {
                if let Term::Const(Literal::String(s)) = kb.get_term(tid) {
                    out.insert(s.clone());
                }
            }
        }
    }
    out
}

/// Detect an equational rule head (WI-139): the head term is an
/// `=` application like `add(?a, ?b) = add(?b, ?a)`. Used by
/// `load_rule` to gate the `rules_by_functor` index — bare equational
/// rules are cite-required only and must not drive automatic SLD
/// rewriting (which would loop on `add_comm`-style laws).
pub fn is_equational_head(kb: &KnowledgeBase, head: TermId) -> bool {
    if let Term::Fn { functor, .. } = kb.get_term(head) {
        // WI-627: classify by RESOLVED SYMBOL, not short name. A genuine `=`/`<=>`
        // equation head carries the canonical `anthill.prelude.PartialEq.eq` /
        // `anthill.kernel.unify` symbol; a carrier's own `eq` op (`Set.eq`,
        // `Map.eq`) is a DIFFERENT symbol that merely shares the short name and
        // must stay a normal, indexed relational rule — not be unindexed as a
        // WI-139 cite-required law. WI-526 (proposal 049): a `<=>`-spelled
        // equation carries `unify` and stays cite-required-by-default exactly like
        // its `=`/`eq` predecessor. (The old `short == "="` disjunct was dead: the
        // pratt desugar mints the functor *string* `"eq"`, never the char `"="`.)
        return kb.is_equality_connective_functor(*functor);
    }
    false
}

/// Test whether a rule's `meta` block contains a flag with the
/// given key. Treats both `[name]` (no value) and `[name: anything]`
/// as "flag is present" — the loader stores the meta as a `meta(...)`
/// term whose `named_args` carry the entries.
pub fn meta_has_flag(kb: &KnowledgeBase, meta: Option<TermId>, key: &str) -> bool {
    let tid = match meta { Some(t) => t, None => return false };
    if let Term::Fn { named_args, .. } = kb.get_term(tid) {
        for (k, _) in named_args.iter() {
            if kb.resolve_sym(*k) == key { return true; }
        }
    }
    false
}

/// WI-087: the value bound to `key` in a `meta(key: value, ...)` term, when the
/// key is present with a value. A flag-form key (`[Marker]`, value `Term::Bottom`)
/// returns `Some(Bottom-tid)` — presence is via [`meta_has_flag`]; this is for
/// valued attributes (`Profile: "cpp20-stl"`, `CppBody: "..."`, `CppName: "..."`).
pub fn meta_value(kb: &KnowledgeBase, meta: Option<TermId>, key: &str) -> Option<TermId> {
    let tid = meta?;
    if let Term::Fn { named_args, .. } = kb.get_term(tid) {
        for (k, v) in named_args.iter() {
            if kb.resolve_sym(*k) == key { return Some(*v); }
        }
    }
    None
}

/// Resolve a `SortRequiresInfo.sort_ref` term to the qualified name
/// of the enclosing scope (sort or operation). Returns the canonical
/// `qualified_name` rather than the short display name so the
/// emitted ProofRecord rule QN is project-unique.
pub fn qn_of_sort_ref(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    match kb.get_term(term) {
        Term::Fn { functor, .. } => Some(kb.qualified_name_of(*functor).to_owned()),
        Term::Ref(s) | Term::Ident(s) => Some(kb.qualified_name_of(*s).to_owned()),
        _ => None,
    }
}

/// WI-390: render a `denoted(value: <inner>)` value-in-type binding to a stable
/// short token for [`flatten_spec`] — by its INNER value (the literal `3` / the
/// ref `c`), NOT the constant functor name `"Denoted"`. Two `requires` differing
/// only in the denoted literal must yield distinct `requires.<SE>` signatures, else
/// their scope axioms collide on one QN and one is silently dropped (load.rs:2592).
fn denoted_value_short(kb: &KnowledgeBase, denoted_tid: TermId) -> String {
    let Term::Fn { named_args, .. } = kb.get_term(denoted_tid) else {
        return "den".to_string();
    };
    let inner = named_args
        .iter()
        .find(|(k, _)| kb.resolve_sym(*k).rsplit('.').next() == Some("value"))
        .map(|(_, t)| *t);
    let Some(inner) = inner else { return "den".to_string() };
    match kb.get_term(inner) {
        Term::Const(Literal::Int(n)) => format!("den_i{n}"),
        Term::Const(Literal::BigInt(n)) => format!("den_i{n}"),
        Term::Const(Literal::Bool(b)) => format!("den_b{b}"),
        Term::Const(Literal::String(s)) => format!("den_str_{s}"),
        Term::Const(Literal::Float(f)) => format!("den_f{}", f.0),
        Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => {
            let n = kb.resolve_sym(*functor);
            format!("den_{}", n.rsplit('.').next().unwrap_or(n))
        }
        _ => "den".to_string(),
    }
}

/// Flatten a `SortRequiresInfo.spec` term to the deterministic
/// short-name signature used in `requires.<SE-flat>` rule QNs. For
/// `SortView(Eq, T = X)` the result is `Eq_<short(X)>`. For a plain
/// nullary sort term `Foo`, the result is `Foo`. Bindings are sorted
/// by their binding key short name to keep the encoding stable
/// across reorderings. Operation auto-bindings (binding values that
/// resolve to operation symbols) are filtered out — they are
/// derived from `resolve_requires_bindings` and not user-written, so
/// they should not pollute the SE-flat. Type-parameter and
/// concrete-sort bindings remain.
pub fn flatten_spec(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    use crate::intern::SymbolKind;
    let term_ref = kb.get_term(term);
    let (functor, pos_args, named_args) = match term_ref {
        Term::Fn { functor, pos_args, named_args } =>
            (*functor, pos_args.clone(), named_args.clone()),
        _ => return None,
    };
    let functor_name = kb.resolve_sym(functor);
    let functor_short = functor_name.rsplit('.').next().unwrap_or(functor_name);
    if functor_short != "SortView" {
        return Some(functor_short.to_owned());
    }
    let base_short = match pos_args.first().map(|t| kb.get_term(*t)) {
        Some(Term::Fn { functor, .. }) | Some(Term::Ref(functor)) | Some(Term::Ident(functor)) => {
            let n = kb.resolve_sym(*functor);
            n.rsplit('.').next().unwrap_or(n).to_owned()
        }
        _ => return None,
    };
    let mut bindings: Vec<(String, String)> = named_args.iter().filter_map(|(k_sym, v_tid)| {
        let value_sym = match kb.get_term(*v_tid) {
            Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => Some(*functor),
            _ => None,
        };
        // Skip operation auto-bindings — they aren't part of the
        // user-written Sort-Expr.
        if let Some(vs) = value_sym {
            if matches!(kb.kind_of(vs), Some(SymbolKind::Operation)) {
                return None;
            }
        }
        let k_name = kb.resolve_sym(*k_sym);
        let k_short = k_name.rsplit('.').next().unwrap_or(k_name).to_owned();
        let v_short = match value_sym {
            // WI-390: a `denoted` value-in-type renders by its inner value so two
            // requires differing only in the literal get distinct signatures.
            Some(s) if kb.qualified_name_of(s) == "anthill.prelude.TypeExtractor.Denoted" => {
                denoted_value_short(kb, *v_tid)
            }
            Some(s) => {
                let n = kb.resolve_sym(s);
                n.rsplit('.').next().unwrap_or(n).to_owned()
            }
            None => match kb.get_term(*v_tid) {
                Term::Const(Literal::String(s)) => format!("str_{s}"),
                _ => "_".to_string(),
            },
        };
        Some((k_short, v_short))
    }).collect();
    bindings.sort_by(|a, b| a.0.cmp(&b.0));
    if bindings.is_empty() {
        Some(base_short)
    } else {
        let parts: Vec<String> = bindings.into_iter().map(|(_, v)| v).collect();
        Some(format!("{base_short}_{}", parts.join("_")))
    }
}

/// Collect the operation symbols from a sort's SortInfo.
fn collect_sort_operations(kb: &mut KnowledgeBase, sort_sym: Symbol) -> Vec<Symbol> {
    let name_field = kb.intern("name");
    let operations_field = kb.intern("operations");

    // WI-671/WI-672 — the SortInfo canonical-sort bucket (or a live scan pre-index); the
    // `Term::Ref(sym) == sort_sym` re-filter below preserves this site's exact match
    // (raw `==` within a canonical bucket returns the same exact fact).
    let rule_ids = crate::kb::typing::sort_info_rids_by_sort(kb, sort_sym);
    for rid in rule_ids {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(head) = kb.fact_head_term(rid) else { continue };
        if let Term::Fn { ref named_args, .. } = kb.get_term(head).clone() {
            let name_matches = named_args.iter()
                .find(|(s, _)| *s == name_field)
                .and_then(|(_, tid)| match kb.get_term(*tid) {
                    Term::Ref(sym) => Some(*sym == sort_sym),
                    _ => None,
                })
                .unwrap_or(false);

            if name_matches {
                let ops_tid = named_args.iter()
                    .find(|(s, _)| *s == operations_field)
                    .map(|(_, t)| *t);
                if let Some(list_tid) = ops_tid {
                    let mut ops = Vec::new();
                    let mut entries = Vec::new();
                    collect_ref_list(kb, list_tid, &mut entries);
                    for (sym, _) in entries {
                        ops.push(sym);
                    }
                    return ops;
                }
            }
        }
    }
    Vec::new()
}

/// Find an operation with the given short name in a sort's OperationInfo facts.
/// Uses the symbol table's scope to check if the operation belongs to the sort.
/// Resolve a `short_name` to an operation declared on the sort named by
/// `sort_ref_tid` (its `OperationInfo` scope equals that sort). Used by the
/// WI-279 dot-dispatch default fallback: `?x.m(args)` resolves `m` against
/// the receiver's least sort.
pub(crate) fn find_operation_in_scope(kb: &mut KnowledgeBase, sort_ref_tid: TermId, short_name: &str) -> Option<Symbol> {
    let op_info_sym = match kb.try_resolve_symbol("anthill.reflect.OperationInfo") {
        Some(sym) => sym,
        None => return None,
    };
    // Get the sort symbol from the sort_ref term
    let sort_sym = match kb.get_term(sort_ref_tid) {
        Term::Fn { functor, .. } => *functor,
        Term::Ref(sym) => *sym,
        _ => return None,
    };

    let rule_ids = kb.rules_by_functor(op_info_sym);
    for rid in rule_ids {
        if !kb.is_fact(rid) {
            continue;
        }
        // WI-348: carrier-agnostic — the OperationInfo head may be a value fact
        // (Node-carrying) for ops with a `denoted` effect. Extract the op
        // symbol from the `name` field through the shared `op_info` helper.
        let op_sym = crate::kb::op_info::head_name_ref(kb, kb.rule_head_value(rid));
        {
            if let Some(op_s) = op_sym {
                // Check if the operation's scope is the sort
                let op_scope_matches = match kb.symbols.get(op_s) {
                    SymbolDef::Resolved { scope_raw, .. } => {
                        // The operation's scope_raw should point to a term whose functor is sort_sym
                        let scope_tid = TermId::from_raw(*scope_raw);
                        match kb.get_term(scope_tid) {
                            Term::Fn { functor, .. } => *functor == sort_sym,
                            _ => false,
                        }
                    }
                    _ => false,
                };

                if op_scope_matches {
                    let op_name = kb.resolve_sym(op_s);
                    let op_short = op_name.rsplit('.').next().unwrap_or(op_name);
                    if op_short == short_name {
                        return Some(op_s);
                    }
                }
            }
        }
    }
    None
}

/// WI-552: wrap a binder/parameter occurrence — a `Ref(s)` / `Ident(s)` that
/// denotes an operation-frame VARIABLE — in its canonical `var_ref(name)` form. A
/// binder *is* a variable; a bare `Ref` denotes a closed global, so emitting a
/// binder as `Ref` is the mis-representation that forced the discharge-time
/// `normalize_param_refs_to_var_ref` patch (WI-067). Doing it here, at the
/// producer (clause / guarded-effect conversion), the guard / precondition
/// carries `var_ref` natively — it unifies with the flow-narrowed Γ fact and
/// floats as the open-world parameter — with no consumer-side normalize.
///
/// "Op-frame variable" is: this signature's `places` (its parameters + `result`,
/// matched by exact symbol) PLUS any callback-parameter/result place
/// (`<op>.f.a` / `<op>.f.result`, matched by the unambiguous `CallbackParam` /
/// `CallbackResult` kinds) — a callback's own binders are equally runtime-unknown
/// and must flounder, so a guard projecting one (`eq(f.result, 0)`) is covered.
/// An existing `var_ref(…)` is not re-wrapped (no double-wrap); a global
/// sort/op/const/constructor ref stays a decidable bare `Ref` (this is why we do
/// NOT use the old `!is_constructor_symbol` net, which over-wrapped globals).
fn wrap_places_as_var_ref(
    kb: &mut KnowledgeBase,
    term: TermId,
    places: &HashSet<Symbol>,
    var_ref_sym: Symbol,
) -> TermId {
    match kb.get_term(term).clone() {
        Term::Ref(s) | Term::Ident(s) if places.contains(&s) || is_callback_place(kb, s) => {
            kb.make_var_ref_term(s)
        }
        Term::Fn { functor, .. } if functor == var_ref_sym => term,
        Term::Fn { .. } => {
            kb.map_fn_children(term, |kb, child| wrap_places_as_var_ref(kb, child, places, var_ref_sym))
        }
        _ => term,
    }
}

/// Is `sym` a callback-parameter / callback-result place (`<op>.f.a` /
/// `<op>.f.result`)? These op-frame binders are registered (by
/// [`register_callback_places`]) into the op scope but NOT into
/// `signature_place_types`, yet they are equally runtime-unknown variables —
/// so a guard / precondition over one must be `var_ref` (flounder), not a bare
/// `Ref`. The `CallbackParam` / `CallbackResult` kinds are unambiguous (unlike
/// `Field`, which also tags ordinary record fields), so matching on them is safe.
fn is_callback_place(kb: &KnowledgeBase, sym: Symbol) -> bool {
    matches!(
        kb.kind_of(sym),
        Some(SymbolKind::CallbackParam | SymbolKind::CallbackResult)
    )
}

/// Build a cons-list from a slice of TermIds: `cons(head: a, tail: cons(head: b, tail: nil()))`.
/// Uses the `anthill.prelude.List` constructors so list operations work.
fn build_list(kb: &mut KnowledgeBase, items: &[TermId]) -> TermId {
    let nil_sym = kb.resolve_symbol("anthill.prelude.List.nil");
    let cons_sym = kb.resolve_symbol("anthill.prelude.List.cons");
    let head_sym = kb.intern("head");
    let tail_sym = kb.intern("tail");

    let mut list = kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });

    for &item in items.iter().rev() {
        list = kb.alloc(Term::Fn {
            functor: cons_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(head_sym, item), (tail_sym, list)]),
        });
    }

    list
}

/// WI-348 — build a carrier-agnostic cons/nil list of `Value`s, the value-fact
/// twin of [`build_list`]. Used for an `OperationInfo` effects list that carries
/// a `Value::Node` label (`Modify[c]`), which cannot live in a `TermId` list.
/// `cons`/`nil` cells are `Value::Entity`s over the same prelude constructors,
/// so the result decomposes into the same `DiscrimKey`s as a term list.
pub(crate) fn build_value_list(kb: &mut KnowledgeBase, items: Vec<crate::eval::value::Value>) -> crate::eval::value::Value {
    use crate::eval::value::Value;
    use std::rc::Rc;
    let nil_sym = kb.resolve_symbol("anthill.prelude.List.nil");
    let cons_sym = kb.resolve_symbol("anthill.prelude.List.cons");
    let head_sym = kb.intern("head");
    let tail_sym = kb.intern("tail");

    let mut list = Value::Entity {
        functor: nil_sym,
        pos: Rc::from(Vec::<Value>::new()),
        named: Rc::from(Vec::<(Symbol, Value)>::new()),
    };
    for item in items.into_iter().rev() {
        list = Value::Entity {
            functor: cons_sym,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(head_sym, item), (tail_sym, list)]),
        };
    }
    list
}

/// WI-341: a homogeneous `OperationInfo` list field (params, effects) as a
/// carrier-agnostic `Value` plus its all-ground flag. All-`Value::Term` items
/// build a hash-consed `Term` cons-list (`Value::Term`); any `Value::Node` builds
/// a value cons-list. The flag drives the head's carrier (a ground head fits a
/// `Term::Fn`; a `Node` anywhere forces a value fact). Shared by the params and
/// effects assembly in `load_operation` so the carrier-selection lives once.
fn value_or_ground_list(
    kb: &mut KnowledgeBase,
    items: Vec<crate::eval::value::Value>,
) -> (crate::eval::value::Value, bool) {
    use crate::eval::value::Value;
    let all_ground = items.iter().all(|v| matches!(v, Value::Term { .. }));
    let list = if all_ground {
        let terms: Vec<TermId> = items
            .iter()
            .map(|v| match v {
                Value::Term { id: t, .. } => *t,
                _ => unreachable!("all_ground"),
            })
            .collect();
        Value::term(build_list(kb, &terms))
    } else {
        build_value_list(kb, items)
    };
    (list, all_ground)
}

/// Build `none()` — the Option.none constructor.
pub(crate) fn build_none(kb: &mut KnowledgeBase) -> TermId {
    let none_sym = kb.resolve_symbol("anthill.prelude.Option.none");
    kb.alloc(Term::Fn {
        functor: none_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    })
}

/// Build `some(value: v)` — the Option.some constructor wrapping a value.
pub(crate) fn build_some(kb: &mut KnowledgeBase, value: TermId) -> TermId {
    let some_sym = kb.resolve_symbol("anthill.prelude.Option.some");
    let value_sym = kb.intern("value");
    kb.alloc(Term::Fn {
        functor: some_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_elem((value_sym, value), 1),
    })
}

// ══════════════════════════════════════════════════════════════════
// Public: convert a parse-time term into a KB term with scope-aware resolution
// ══════════════════════════════════════════════════════════════════

/// Convert a parse-time term (from `SimpleTermStore`) into the KB's
/// hash-consed `TermStore`, resolving symbols through the KB's scope chain.
///
/// `scope_raw` is the scope in which to resolve names (typically `_global`).
/// `var_map` preserves variable identity: two `?x` in a query share the same
/// `VarId`. Pass an empty map on the first call; reuse the same map across
/// multiple terms that should share variables.
pub fn convert_query_term(
    kb: &mut KnowledgeBase,
    parse_terms: &SimpleTermStore,
    parse_symbols: &crate::intern::SymbolTable,
    parse_id: TermId,
    scope_raw: u32,
    var_map: &mut HashMap<u32, VarId>,
) -> TermId {
    let parse_term = parse_terms.get(parse_id).clone();
    match parse_term {
        Term::Const(lit) => kb.alloc(Term::Const(lit)),
        Term::Var(Var::Global(vid)) => {
            let kb_vid = if let Some(&mapped) = var_map.get(&vid.raw()) {
                mapped
            } else {
                let name_str = parse_symbols.name(vid.name());
                let kb_name = kb.intern(name_str);
                let new_vid = kb.fresh_var(kb_name);
                var_map.insert(vid.raw(), new_vid);
                new_vid
            };
            kb.alloc(Term::Var(Var::Global(kb_vid)))
        }
        Term::Var(Var::DeBruijn(n)) => kb.alloc(Term::Var(Var::DeBruijn(n))),
        Term::Var(Var::Rigid(_)) => {
            // Rigid vars are introduced only post-open by the resolver,
            // never present in stored terms — should not appear here.
            unreachable!("Var::Rigid in stored parse term")
        }
        Term::Fn { functor, pos_args, named_args } => {
            let functor_name = parse_symbols.name(functor);
            let kb_functor = resolve_name_in_kb(kb, functor_name, scope_raw);
            let mut new_pos: SmallVec<[TermId; 4]> = pos_args
                .iter()
                .map(|&id| convert_query_term(kb, parse_terms, parse_symbols, id, scope_raw, var_map))
                .collect();
            let mut new_named: SmallVec<[(Symbol, TermId); 2]> = named_args
                .iter()
                .map(|&(sym, id)| {
                    let n = parse_symbols.name(sym);
                    let kb_sym = kb.intern(n);
                    (kb_sym, convert_query_term(kb, parse_terms, parse_symbols, id, scope_raw, var_map))
                })
                .collect();

            // WI-433: DESUGAR a positional constructor QUERY to the canonical
            // NAMED form, mirroring the fact/rule term path
            // (`convert_term_with_expected`) so a CLI query `WorkItem(?, Verified(?))`
            // matches the named-arg facts via the discrim tree. Positional args fill
            // the fields NOT already given by name, in declaration order (the same
            // rank-among-not-named rule). Reflect / `anthill.reflect.*` meta-ctors
            // keep their positional shape. A query is transient with no load error
            // channel, so an over-arity query is left positional (it simply finds no
            // match) rather than aborting — unlike a stored fact/rule, a malformed
            // query corrupts nothing.
            if !new_pos.is_empty() {
                let named_syms: SmallVec<[Symbol; 2]> = new_named.iter().map(|(s, _)| *s).collect();
                // A transient query has no load-error channel, so an over-arity
                // query is left positional (it simply finds no match) rather than
                // aborting — only the `Assign` plan rewrites.
                if let PositionalPlan::Assign(fields) =
                    kb.positional_to_named_plan(kb_functor, &named_syms, new_pos.len())
                {
                    for (i, pos_val) in new_pos.drain(..).enumerate() {
                        new_named.push((fields[i], pos_val));
                    }
                }
            }

            // Expand partial named args: fill missing entity fields with fresh vars
            // Always sort named args to match entity field order (required for
            // discrimination tree matching — both facts and patterns must have
            // named args in the same order). Positional args also count as
            // "provided" — `ToolPasses("cargo-test")` covers `tool` via
            // pos_args[0], so the field shouldn't be re-stuffed with a fresh
            // var in named (which would shadow the positional value at
            // materialization time).
            if let Some(all_fields) = kb.entity_field_names(kb_functor) {
                let all_fields = all_fields.to_vec();
                if new_named.len() + new_pos.len() < all_fields.len() {
                    let mut provided: HashSet<Symbol> = new_named
                        .iter().map(|(s, _)| *s).collect();
                    for (i, &field_sym) in all_fields.iter().enumerate() {
                        if i < new_pos.len() {
                            provided.insert(field_sym);
                        }
                    }
                    for &field_sym in &all_fields {
                        if !provided.contains(&field_sym) {
                            let fresh = kb.fresh_var(field_sym);
                            let var_term = kb.alloc(Term::Var(Var::Global(fresh)));
                            new_named.push((field_sym, var_term));
                        }
                    }
                }
                let order: HashMap<Symbol, usize> = all_fields.iter().enumerate()
                    .map(|(i, &s)| (s, i)).collect();
                new_named.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
            }

            kb.alloc(Term::Fn { functor: kb_functor, pos_args: new_pos, named_args: new_named })
        }
        Term::Ident(sym) => {
            let name = parse_symbols.name(sym);
            if let Some(resolved) = resolve_name_in_kb_opt(kb, name, scope_raw) {
                kb.alloc(Term::Ref(resolved))
            } else {
                let kb_sym = kb.intern(name);
                kb.alloc(Term::Ident(kb_sym))
            }
        }
        Term::Ref(sym) => {
            let name = parse_symbols.name(sym);
            let kb_sym = resolve_name_in_kb(kb, name, scope_raw);
            kb.alloc(Term::Ref(kb_sym))
        }
        Term::Bottom => kb.alloc(Term::Bottom),
        Term::ParseAux(aux) => {
            // WI-366 B1: a written effect-row binding value in a query pattern
            // (`anthill query --pattern 'Spec[E = {}]'`). A parse `Term` can't
            // structurally hold a row, so it rides as `ParseAux::TypeExpr(
            // EffectRow)`. This converter is a free fn (no `Loader`), so it can't
            // reuse `lower_effect_row`; build the EMPTY (closed-pure) row directly
            // — the same `effects_rows(empty_row)` the loader emits, so the pattern
            // matches `provides`/fact rows. A non-empty written row can carry
            // labels a query term can't faithfully lower without the loader's type
            // machinery → match permissively with a fresh row var, rather than
            // panicking (the pre-WI-366-B1 behavior was a loud `unresolved name`
            // error; a written `{}` query is the realistic pattern).
            match aux.as_ref() {
                ParseAux::TypeExpr(TypeExpr::EffectRow(effects)) if effects.is_empty() => {
                    kb.build_canonical_effects_rows(&[])
                }
                ParseAux::TypeExpr(TypeExpr::EffectRow(_)) => {
                    let n = kb.intern("_E");
                    let v = kb.fresh_var(n);
                    kb.alloc(Term::Var(Var::Global(v)))
                }
                other => unreachable!(
                    "parse-only Term::ParseAux({other:?}) reached convert_query_term — \
                     only a written effect-row binding value is handled here",
                ),
            }
        }
    }
}

/// Resolve a name in the KB: try qualified name first, then scope-aware resolution,
/// then fall back to intern.
fn resolve_name_in_kb(kb: &mut KnowledgeBase, name: &str, scope_raw: u32) -> Symbol {
    resolve_name_in_kb_opt(kb, name, scope_raw)
        .unwrap_or_else(|| kb.intern(name))
}

/// Try to resolve a name in the KB: qualified name first, then scope-aware
/// resolution. WI-476: there is NO global short-name fallback — a name resolves
/// only within its local environment (qualified path / enclosing scope / imports
/// / `requires`). An unresolved name returns `None`, and the caller interns it as
/// a bare symbol (a data name in a query pattern), surfacing a genuine
/// missing-import as a non-matching query rather than silently rescuing it.
fn resolve_name_in_kb_opt(kb: &KnowledgeBase, name: &str, scope_raw: u32) -> Option<Symbol> {
    if let Some(&sym) = kb.symbols.by_qualified_name.get(name) {
        // WI-369: the qualified path bypasses `resolve_in_scope`'s `internal`
        // filter, so apply the visibility gate here. A hidden-internal hit falls
        // through to the (also-filtered) scope walk and resolves to `None`.
        if kb.symbols.internal_visible_from(sym, scope_raw) {
            return Some(sym);
        }
    }
    match kb.symbols.resolve_in_scope(name, scope_raw) {
        ResolveResult::Found(sym) => Some(sym),
        // WI-040 / WI-521: reserved kernel desugaring vocab AND the implicit
        // prelude resolve directly to their qualified home in query patterns too —
        // parity with `remap_name_str`, so a reflection query naming `field_access`
        // / `ListLiteral` or a prelude name like `eq` / `cons` bare still matches
        // after the `_global` imports were removed. Fallback only: scope resolution
        // already failed, so a user-defined same-spelling name has won. (Distinct
        // from WI-476's deliberate no-rescue for arbitrary user short-names — these
        // are RESERVED / PRELUDE names that always denote their target.)
        _ => implicit_qualified(name)
            .and_then(|qn| kb.symbols.by_qualified_name.get(qn).copied()),
    }
}

// WI-233: per-item-kind aggregator (count, total time). Gated by
// ANTHILL_ITEM_TIMING=1. Aggregates across all files in a pass; the
// outer phase reset+print helpers below.
thread_local! {
    static ITEM_TIMINGS: std::cell::RefCell<std::collections::HashMap<&'static str, (u32, std::time::Duration)>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

pub fn reset_item_timings() {
    ITEM_TIMINGS.with(|m| m.borrow_mut().clear());
}

pub fn print_item_timings(label: &str) {
    ITEM_TIMINGS.with(|m| {
        let m = m.borrow();
        let mut entries: Vec<_> = m.iter().collect();
        entries.sort_by_key(|(_, (_, d))| std::cmp::Reverse(*d));
        eprintln!("[item_timing/{label}]");
        for (kind, (count, total)) in entries {
            eprintln!("  {kind:>16}: {count:>5} items, {total:?}");
        }
    });
}

/// Work-stack opcode for the iterative expression loader. `Visit`
/// dispatches a parse-time term (leaf → emit kb_id; non-leaf → push
/// a `Build` frame + child `Visit`s). `Build` consumes
/// already-converted children from the result stack and assembles
/// the parent kb_id, keeping host stack usage O(1) regardless of
/// source nesting depth.
enum LoadWorkOp {
    Visit(TermId),
    Build(LoadBuildFrame),
    /// Open a let/lambda/match-branch local-name scope. The frame's
    /// (name → symbol) entries shadow same-named rules / params /
    /// constructors / etc. during the body's visit, so the body's
    /// bare-name reference resolves to the let-bound symbol instead
    /// of an unrelated same-short-name definition elsewhere.
    PushLocalScope(HashMap<String, Symbol>),
    /// Close the topmost local-name scope. Paired with a preceding
    /// `PushLocalScope` so push/pop nest correctly under iterative
    /// dispatch.
    PopLocalScope,
    /// WI-304: enter occurrence-suppression for a let/lambda/match pattern
    /// subtree. The term walk visits the pattern as a child, but in the
    /// occurrence the pattern lives in a `TermId` field (not a child
    /// occurrence), so the pattern subtree must push NOTHING to
    /// `expr_occ_results`. Nests via a counter.
    PushOccSuppress,
    /// WI-304: leave occurrence-suppression (pairs with `PushOccSuppress`).
    PopOccSuppress,
}

/// Post-order assembly frame for the iterative expression loader.
/// Each variant pairs an `outer_parse_id` (consumed by the final
/// `create_occurrence` span record) with the structural metadata
/// (counts, names, functors) needed to drain the right number of
/// converted children from the result stack and rebuild the parent.
enum LoadBuildFrame {
    MatchExpr {
        outer_parse_id: TermId,
        branch_count: usize,
    },
    MatchBranch {
        outer_parse_id: TermId,
        has_guard: bool,
    },
    IfExpr {
        outer_parse_id: TermId,
    },
    LetExpr {
        outer_parse_id: TermId,
    },
    Lambda {
        outer_parse_id: TermId,
    },
    /// WI-538: an in-body / control-flow proof. `has_conclude` selects
    /// whether the result stack carries `[body, conclude]` or `[body]`;
    /// the target / strategy / using clauses are read back off the
    /// parse term's `ParseAux::ProofStmt`.
    ProofStmt {
        outer_parse_id: TermId,
        has_conclude: bool,
    },
    PatternConstructor {
        outer_parse_id: TermId,
        name_ref: TermId,
        sub_pattern_count: usize,
        /// WI-445: the (reinterned) field names of named sub-patterns
        /// (`Box(v: some(x))`), in the order their sub-patterns are visited
        /// — drained alongside `sub_pattern_count` positional results.
        named_fields: Vec<Symbol>,
    },
    PatternTuple {
        outer_parse_id: TermId,
        element_count: usize,
    },
    ApplyOrConstructor {
        outer_parse_id: TermId,
        functor: Symbol,
        pos_count: usize,
        named_keys: SmallVec<[Symbol; 2]>,
    },
    /// WI-278: re-encode a parse `dot_apply(receiver, Ident(name),
    /// ...args)` into the reflect `dot_apply(receiver, name: Ref,
    /// args: List[ApplyArg])`. `name_ref` is pre-resolved (the name is
    /// metadata, not a child); the receiver and args are drained from
    /// `results`.
    DotApply {
        outer_parse_id: TermId,
        name_ref: TermId,
        pos_count: usize,
        named_keys: SmallVec<[Symbol; 2]>,
    },
}

struct Loader<'a> {
    kb: &'a mut KnowledgeBase,
    parsed: &'a ParsedFile,
    #[allow(dead_code)]
    resolver: &'a dyn SourceResolver,
    #[allow(dead_code)]
    loaded_paths: &'a mut HashSet<String>,
    // Map from parse-time TermId → KB TermId
    term_map: HashMap<u32, TermId>,
    // Map from parse-time Symbol → KB Symbol (for reintern — plain intern)
    sym_map: HashMap<u32, Symbol>,
    // Map from parse-time VarId → KB VarId
    var_map: HashMap<u32, VarId>,
    errors: Vec<LoadError>,
    // Current scope for scope-aware resolution
    current_scope: TermId,
    // Cache: type param name → TermId (Var) per scope, so all references to T share the same Var
    type_param_vars: HashMap<(u32, String), TermId>,
    // WI-341 loader binder context: while loading a callback PARAMETER's arrow
    // type, its arrow param names (`a`, `t`) are bound here to their registered
    // `CallbackParam` place symbols (`<op>.f.a`), so a self-referential arrow
    // effect like `Modify[a]` resolves to the place `<op>.f.a` (the binder's
    // canonical name from the op frame, doc §2) rather than failing as an
    // unresolved name. Empty except during that one arrow-type conversion.
    arrow_binder_scope: HashMap<String, Symbol>,
    // WI-440: true while lowering the INNER label of a `-E` absence atom
    // (`TypeExpr::EffectAbsent`). An unresolved name there is upgraded from the
    // advisory `UnresolvedName` to the load-BLOCKING `ValueInTypeNotResolved`:
    // a typo'd place (`-Modify[zzz]`) would otherwise load as a vacuous
    // constraint with only a warning — silently unenforced.
    in_effect_absence: bool,
    // WI-429: true while lowering a TYPE expression (`type_expr_to_child` and
    // everything beneath it). An unresolvable Capitalized DOTTED name there is
    // upgraded from the advisory `UnresolvedName` (+ degenerate minted nominal)
    // to the load-blocking `UnresolvedTypeName` — a typo'd `Sort.Member` /
    // `s.Member` spelling must never load as an opaque nominal sort literally
    // named "Sort.Member".
    in_type_position: bool,
    // WI-529: true while building an OPERATION BODY (`convert_expr_term`), which is
    // EVALUATED, not resolved. The boolean operators `not`/`or` are position-directed:
    // a value expression in an op body means the dispatched Bool VALUE op
    // (`Bool.not`/`Bool.or`, which have eval builtins), whereas a rule-body goal means
    // the resolver primitive (`reflect.not` NAF / `kernel.or` disjunction, which have
    // NO eval builtin). This flag selects the Bool target in `remap_name_str`; outside
    // an op body the primitives stay the default. (`and` is value-only — handled by the
    // general fallback — and `neg`→`Numeric.neg` is not position-directed.)
    in_op_body_value: bool,
    // WI-605: set by the bare-arrow diagnostic arm when it substitutes a
    // `Term::Bottom` recovery leaf into the body being converted. Cleared at
    // `convert_expr_term` entry; read by `load_operation` / `load_const` to
    // SKIP storing the poisoned body node — the typer's loud `Expr::Bottom`
    // post-elaboration invariant would otherwise stack a second,
    // internal-jargon error on top of the targeted `ArrowTermInExprPosition`.
    expr_body_bottom_recovery: bool,
    // WI-582: active while converting a rule HEAD, so `convert_term`'s
    // `typed_var` strip records the per-variable type bound (`?x: T`) into
    // `rule_head_type_bounds` instead of treating the marker as a generic term.
    // A `typed_var` reaching `convert_term` with this false is a misuse (a type
    // annotation on a variable outside a rule pattern) and is reported loudly.
    in_rule_head: bool,
    // WI-710: nesting depth inside `convert_term_with_expected` — 1 while converting a
    // TOP-LEVEL term (a `fact` head, a rule head / body goal), >1 for a term nested as
    // another term's argument. It tells the two readings of one syntax apart: a
    // sort-headed term at top level is an INSTANCE CLAIM, whose argument grammar is the
    // instance-fact one (type-param bindings, plus op bindings for an op-bearing fact
    // like `fact Monad[M = Option, pure = optionPure]`, plus the WI-407 carrier slot of
    // `fact NonMonotonicStore[FileStore]`); NESTED, it is a parameterized TYPE
    // (`is_modifiable(Cell[V = Int64])`), whose arguments are type arguments and nothing
    // else. Only the nested reading gets the WI-709 type-argument check.
    term_depth: usize,
    // WI-716: true while converting a VALUE position — a ground fact head
    // (`load_fact`) or an entity-DERIVING rule head (`load_rule`). There the
    // partial-named-arg expansion fills an absent OPTIONAL field with `none()`
    // (value semantics); in a query/rule-body PATTERN (and for an absent REQUIRED
    // field) it fills a fresh var. A var in a value slot would make the produced
    // entity `forall v. E(field: v)` and unsoundly unify a `some(?)` pattern.
    // CLEARED inside a reflect `Term`-typed field, whose content is a quoted
    // pattern, not a value (see `convert_arg_value`).
    in_value_position: bool,
    // WI-582: per-head accumulator of (head variable, declared-type bound) pairs
    // collected while converting a typed rule head; drained by `load_rule` after
    // each head, mapped to DeBruijn indices, and installed on the RuleEntry as
    // per-variable `Type` bounds (the typed-rule-pattern firing guard).
    rule_head_type_bounds: Vec<(VarId, TermId)>,
    // WI-582: the `[T]` type-variable-introducer form's desugar table. A rule
    // `keep[T](?x: T, ?y) = ?x :- Spec[T]` is the verbose spelling of the inline
    // `keep(?x: Spec, ?y) = ?x`. Before converting the head, `load_rule` maps each
    // head-introduced type-var (`[T]`) to the bound its body guard `Spec[T]`
    // gives it; the `typed_var` strip then resolves `?x: T` to that bound. Keyed
    // by the introducer's short name; empty for the inline form and untyped rules.
    rule_tvar_bounds: HashMap<String, TermId>,
    // Description index counter per target (keyed by TermId raw)
    desc_index: HashMap<u32, i64>,
    // ── Occurrence tracking ─────────────────────────────────────
    // Source file id for this file's occurrences
    source_id: SourceId,
    // Symbol of the current owning declaration (operation, rule, etc.)
    current_owner: Option<Symbol>,
    // Sort/enum terms defined in this file (for targeted type checking)
    defined_sorts: Vec<TermId>,
    // RuleIds of top-level user `fact …(…)` blocks, in source order.
    // Persistence backends (IndexedFileStore et al.) zip this with the
    // corresponding parsed.fact_spans() to populate per-fact source maps
    // so retract can drop a specific block without reconstructing it
    // from a content fingerprint.
    fact_rule_ids: Vec<crate::kb::RuleId>,
    // Pre-resolved symbols for the iterative expression loader. The 15
    // keys below are hit on every non-leaf node in `build_load` — caching
    // them once at `Loader::new` avoids repeated hashmap lookups in the
    // hot path.
    expr_syms: ExprBuilderSyms,
    // Reusable work / result stacks for `convert_expr_term`. Kept on
    // the loader and `mem::take`-swapped at each entry so a single pair
    // of allocations amortizes across every operation body.
    expr_work: Vec<LoadWorkOp>,
    expr_results: Vec<TermId>,
    // WI-304: parallel occurrence-result stack for `convert_expr_term`. As
    // the term walk builds each KB Term, the matching `NodeOccurrence` is
    // built natively here, so an op body's occurrence tree is produced
    // directly rather than re-inferred from the term via
    // `materialize_from_handle`.
    expr_occ_results: Vec<Rc<NodeOccurrence>>,
    // WI-304: match-branch metadata captured at each MatchBranch build, drained
    // by the enclosing MatchExpr build into a `BuildFrame::Match`.
    expr_match_metas: Vec<node_occurrence::BranchMeta>,
    // WI-304: occurrence-suppression depth. While > 0 (inside a let/lambda/
    // match pattern subtree) the leaf/build arms push nothing to
    // `expr_occ_results` — the pattern is a `TermId` field, not a child.
    occ_suppress: usize,
    // Stack of local-name scopes opened by `let`, `lambda`, and
    // `match_branch` during expression conversion. Each entry maps a
    // short name to its KB Symbol (the pattern's interned bare symbol).
    // Name resolution in `remap_symbol` consults this stack before
    // walking the `current_scope` chain so a body's reference to a
    // let-bound name doesn't accidentally resolve to an unrelated
    // rule / op / param of the same short name elsewhere in scope.
    // Pushed by the let/match/lambda visit arms; popped by
    // `LoadWorkOp::PopLocalScope`.
    local_names_stack: Vec<HashMap<String, Symbol>>,
    // WI-550: per-binding-site alpha-rename map — a `pattern_var` parse-node raw
    // id → the FRESH unique Symbol minted for that binder (`kb.intern_unique`).
    // The local-name frame (consulted by body references) and `load_pattern_var`
    // (the binding occurrence the typer reads as `Pattern::Var`) both resolve a
    // binder through `binder_sym`, which mints once per site and caches here, so
    // the two agree on ONE identity per binding while `let x = 0; let x = 1` mint
    // DISTINCT symbols — making Γ's binder facts (`x ≡ e`, `eq(s, some(x))`)
    // shadowing-correct (proposal 050). Parse ids are unique per file (the parse
    // store does not hash-cons), so no two binding sites collide.
    binder_syms: HashMap<u32, Symbol>,
    // WI-201: bare-spec-member sugar accumulator. `Some` ONLY while loading an
    // operation SIGNATURE (set up at the top of `load_operation`, drained at its
    // end). A bare `Spec.Member` in a signature type position — `Member` a
    // declared type-param of the spec sort `Spec`, no carrier in scope — lowers
    // CARRIER-DIRECT (design path-dependent-types.md §5.4 / WI-201, user-confirmed
    // 2026-06-16) to a fresh op type-param `?P` (the type at that position IS `?P`)
    // plus a synthesized `requires Spec[Member = ?P]`. Deduped per `(spec, member)`
    // so two `WorkItemStore.State` refs in one signature share one `?P`; a distinct
    // operation gets a fresh accumulator → a distinct `?P`. Outside an op signature
    // the field is `None`, so the bare-spec arm keeps its loud `RigidTypeProjection`
    // conflation error (the sugar never fires for sort/entity/fact type positions).
    bare_spec_sugar: Option<BareSpecSugar>,
    // WI-201: carrier bindings of the sort CURRENTLY being loaded — `(spec base sym,
    // member sym)` → the bound value term, pre-scanned from the sort's `provides` /
    // `fact` items BEFORE any operation in its body is loaded (so it is order-
    // independent). Lets the bare-spec sugar NARROW `Spec.Member` to the concrete
    // carrier an enclosing impl binds (`fact WorkItemStore[State = WIS]` ⟹
    // `WorkItemStore.State` ≡ WIS inside that sort) instead of minting a fresh
    // existential. Empty outside a sort body; saved/restored around nested sorts.
    current_sort_carrier_bindings: HashMap<(Symbol, Symbol), TermId>,
    // WI-489: the statically-known type of each VALUE PLACE in the operation
    // signature CURRENTLY being loaded — param symbols → their declared type, the
    // `result` binder → the return type. Populated in `load_operation` BEFORE the
    // effects clause is converted (return + params come first), so a value-in-type
    // field projection (`Modify[result.a]`, `Modify[c.backend]`) can validate its
    // field path against the head's concrete type at load (`try_denoted_value_path`)
    // and reject a non-existent field loudly. Empty outside an operation signature
    // (a local / cross-context head is absent ⇒ validation defers, never rejects).
    signature_place_types: HashMap<Symbol, Value>,
}

/// WI-201: per-operation accumulator for the carrier-direct bare-spec-member sugar.
/// Built fresh per `load_operation`; drained into the op's `type_params` (the minted
/// `?P` vars) and `requires` (the `Spec[Member = ?P]` clauses, rebuilt from `minted`)
/// once the whole signature has been converted.
#[derive(Default)]
struct BareSpecSugar {
    /// Dedup + insertion order: `(spec base sym, member sym)` → the minted `?P` var
    /// term. A repeated `Spec.Member` in the same signature reuses its `?P`. The sole
    /// source for the drain — the requires clause `Spec[Member = ?P]` is reconstructed
    /// from each entry, so there is no second list to keep in sync.
    minted: Vec<((Symbol, Symbol), TermId)>,
}

/// WI-489: the outcome of resolving one field segment of a value-in-type projection
/// against the running type ([`Loader::field_step_in_value`]).
enum FieldStep {
    /// The field exists; carries its declared type so a multi-level walk continues.
    Found(Value),
    /// A CONCRETE data type (entity / named-tuple) that does not declare the field —
    /// a loud rejection. `type_display` names the type for the diagnostic.
    NoField { type_display: String },
    /// The running type is not a concretely-known data shape (abstract type-param,
    /// spec/builtin with no registered fields, arrow, effect row, projection neutral):
    /// the field is only knowable at the elimination site, so validation defers.
    Defer,
}

/// Pre-resolved symbols used by `build_load`. Populated once at
/// `Loader::new`; all named-arg keys + functor symbols for the kb
/// canonical Expr / Pattern shape live here so the iterative loader
/// never re-hashes the same string.
/// WI-630: reflect symbols + the `Sort` meta-sort term for `EntityInfo`
/// emission, resolved once by [`Loader::entity_info_syms`] and threaded into
/// [`Loader::emit_entity_info`] so a sort's entity loop does not re-resolve them
/// per entity.
struct EntityInfoSyms {
    field_info: Symbol,
    entity_info: Symbol,
    name: Symbol,
    type_name: Symbol,
    fields: Symbol,
    sort_sort: TermId,
}

struct ExprBuilderSyms {
    match_expr: Symbol,
    match_branch: Symbol,
    if_expr: Symbol,
    let_expr: Symbol,
    lambda: Symbol,
    proof_stmt: Symbol,
    constructor_pattern: Symbol,
    tuple_pattern: Symbol,
    constructor: Symbol,
    apply: Symbol,
    dot_apply: Symbol,
    apply_arg: Symbol,
    k_scrutinee: Symbol,
    k_branches: Symbol,
    k_pattern: Symbol,
    k_guard: Symbol,
    k_body: Symbol,
    k_cond: Symbol,
    k_then: Symbol,
    k_else: Symbol,
    k_value: Symbol,
    k_param: Symbol,
    k_target: Symbol,
    k_strategy: Symbol,
    k_conclude: Symbol,
    k_name: Symbol,
    k_receiver: Symbol,
    k_args: Symbol,
    k_named: Symbol,
    k_elements: Symbol,
    k_fn: Symbol,
    k_type_args: Symbol,
    type_arg: Symbol,
}

impl ExprBuilderSyms {
    fn new(kb: &mut KnowledgeBase) -> Self {
        Self {
            match_expr: kb.resolve_symbol("anthill.reflect.Expr.match_expr"),
            match_branch: kb.resolve_symbol("anthill.reflect.MatchBranch"),
            if_expr: kb.resolve_symbol("anthill.reflect.Expr.if_expr"),
            let_expr: kb.resolve_symbol("anthill.reflect.Expr.let_expr"),
            lambda: kb.resolve_symbol("anthill.reflect.Expr.lambda_expr"),
            proof_stmt: kb.resolve_symbol("anthill.reflect.Expr.proof_stmt"),
            constructor_pattern: kb.resolve_symbol("anthill.reflect.Pattern.constructor_pattern"),
            tuple_pattern: kb.resolve_symbol("anthill.reflect.Pattern.tuple_pattern"),
            constructor: kb.resolve_symbol("anthill.reflect.Expr.constructor"),
            apply: kb.resolve_symbol("anthill.reflect.Expr.apply"),
            dot_apply: kb.resolve_symbol("anthill.reflect.Expr.dot_apply"),
            apply_arg: kb.resolve_symbol("anthill.reflect.ApplyArg"),
            k_scrutinee: kb.intern("scrutinee"),
            k_branches: kb.intern("branches"),
            k_pattern: kb.intern("pattern"),
            k_guard: kb.intern("guard"),
            k_body: kb.intern("body"),
            k_cond: kb.intern("cond"),
            k_then: kb.intern("then_branch"),
            k_else: kb.intern("else_branch"),
            k_value: kb.intern("value"),
            k_param: kb.intern("param"),
            k_target: kb.intern("target"),
            k_strategy: kb.intern("strategy"),
            k_conclude: kb.intern("conclude"),
            k_name: kb.intern("name"),
            k_receiver: kb.intern("receiver"),
            k_args: kb.intern("args"),
            k_named: kb.intern("named"),
            k_elements: kb.intern("elements"),
            k_fn: kb.intern("fn"),
            k_type_args: kb.intern("type_args"),
            type_arg: kb.intern("type_arg"),
        }
    }
}

impl<'a> Loader<'a> {
    fn new(
        kb: &'a mut KnowledgeBase,
        parsed: &'a ParsedFile,
        resolver: &'a dyn SourceResolver,
        loaded_paths: &'a mut HashSet<String>,
        global_scope: TermId,
    ) -> Self {
        let source_id = kb.sources.register("<unknown>".to_string());
        let expr_syms = ExprBuilderSyms::new(kb);
        Self {
            kb,
            parsed,
            resolver,
            loaded_paths,
            term_map: HashMap::new(),
            sym_map: HashMap::new(),
            var_map: HashMap::new(),
            errors: Vec::new(),
            current_scope: global_scope,
            desc_index: HashMap::new(),
            type_param_vars: HashMap::new(),
            arrow_binder_scope: HashMap::new(),
            in_effect_absence: false,
            in_type_position: false,
            in_op_body_value: false,
            expr_body_bottom_recovery: false,
            defined_sorts: Vec::new(),
            fact_rule_ids: Vec::new(),
            source_id,
            current_owner: None,
            in_rule_head: false,
            term_depth: 0,
            in_value_position: false,
            rule_head_type_bounds: Vec::new(),
            rule_tvar_bounds: HashMap::new(),
            expr_syms,
            expr_work: Vec::with_capacity(64),
            expr_results: Vec::with_capacity(64),
            expr_occ_results: Vec::new(),
            expr_match_metas: Vec::new(),
            occ_suppress: 0,
            local_names_stack: Vec::new(),
            binder_syms: HashMap::new(),
            bare_spec_sugar: None,
            current_sort_carrier_bindings: HashMap::new(),
            signature_place_types: HashMap::new(),
        }
    }

    /// WI-550: the FRESH unique Symbol for a binding site, minted once per
    /// `pattern_var` parse node and cached in `binder_syms`. Both the local-name
    /// frame (`collect_pattern_names_into`, read by body references) and the
    /// pattern occurrence (`load_pattern_var`, read by the typer as
    /// `Pattern::Var`) resolve a binder through here, so the two share ONE
    /// identity per site, while distinct sites (`let x = 0; let x = 1`) get
    /// distinct symbols — alpha-renaming the binder so Γ's facts over it are
    /// shadowing-correct. The display name stays `name`, so eval's name-based
    /// `find_local` and the printer are unchanged.
    fn binder_sym(&mut self, name: &str, pattern_var_parse_id: TermId) -> Symbol {
        if let Some(&sym) = self.binder_syms.get(&pattern_var_parse_id.raw()) {
            return sym;
        }
        let sym = self.kb.intern_unique(name);
        self.binder_syms.insert(pattern_var_parse_id.raw(), sym);
        sym
    }

    /// Look up a name in the let/lambda/match-branch scope stack.
    /// Returns the bound KB symbol when the name is in scope.
    fn lookup_local_name(&self, name: &str) -> Option<Symbol> {
        for frame in self.local_names_stack.iter().rev() {
            if let Some(&sym) = frame.get(name) {
                return Some(sym);
            }
        }
        None
    }

    /// WI-618: walk a rule / fact / constraint / contract PARSE term and flag
    /// any minted arrow (`arrow`/`arrow_effect`, i.e. an infix `->`) whose
    /// subtree contains a binder-looking leaf name resolving to nothing —
    /// the keyword-less `pattern -> body` lambda typo. Unlike the op/const
    /// body case (`ArrowTermInExprPosition`, where a bare arrow is always an
    /// error), arrow-as-TYPE is legitimate in these term positions (types are
    /// terms), so provenance alone cannot condemn the term; the unresolvable
    /// binder-looking leaf is what distinguishes the typo from a real arrow
    /// type, whose leaves — sorts, type params, param/`result` places —
    /// resolve, and whose logical variables are `?`-vars, not bare names.
    ///
    /// `bound` carries names that are legitimately in scope but invisible to
    /// `resolve_in_scope`: WI-582 rule type-vars (`[t]` introducers live in
    /// `rule_tvar_bounds`, never the symbol table) seeded by the caller, plus
    /// binders of `lambda`/`let`/`match` forms met during the walk (their
    /// local frames only exist in the later load walk, not in this pre-pass).
    ///
    /// A minted arrow is checked ONCE and not recursed into: a nested arrow's
    /// leaves are a subset of the outer's, so the outer verdict covers it.
    /// A WRITTEN call named `arrow` is not an arrow term — its args are
    /// walked normally (they may contain minted arrows of their own).
    fn check_bare_arrow_typo(
        &mut self,
        parse_id: TermId,
        position: &'static str,
        bound: &HashSet<String>,
    ) {
        let functor = match self.parsed.terms.get(parse_id) {
            Term::Fn { functor, .. } => *functor,
            _ => return,
        };
        let (is_arrow, binder_layout) = {
            let name = self.parsed.symbols.name(functor);
            (pratt::is_arrow_functor(name), binder_form_layout(name))
        };
        if is_arrow && self.parsed.terms.is_minted(parse_id) {
            if let Some(unresolved) = self.first_unresolvable_arrow_leaf(parse_id, bound) {
                self.errors.push(LoadError::BareArrowInLogicPosition {
                    position,
                    unresolved,
                    span: self.parsed.terms.span(parse_id),
                });
            }
            return;
        }
        let (pos_args, named_args) = match self.parsed.terms.get(parse_id) {
            Term::Fn { pos_args, named_args, .. } => (pos_args.clone(), named_args.clone()),
            _ => unreachable!("checked to be Term::Fn above"),
        };
        // Provenance + arity gate: a user-written call merely NAMED like a
        // binder form (not converter-minted, or lacking the binder arity)
        // gets the generic recursion, not the scoped walk — its args are
        // ordinary references, and slot-skipping them could hide a typo
        // arrow sitting in the "pattern" position.
        let minted_binder = binder_layout
            .filter(|_| self.parsed.terms.is_minted(parse_id))
            .and_then(|(pat_idx, scoped_from)| {
                pos_args.get(pat_idx).map(|&pat| (pat_idx, scoped_from, pat))
            });
        if let Some((pat_idx, scoped_from, pat)) = minted_binder {
            let mut inner = bound.clone();
            self.pattern_binder_names(pat, &mut inner);
            for (i, &child) in pos_args.iter().enumerate() {
                if i == pat_idx {
                    continue; // the pattern binds, it doesn't reference
                }
                let scope = if i >= scoped_from { &inner } else { bound };
                self.check_bare_arrow_typo(child, position, scope);
            }
            for &(_, child) in &named_args {
                self.check_bare_arrow_typo(child, position, &inner);
            }
            return;
        }
        for &child in &pos_args {
            self.check_bare_arrow_typo(child, position, bound);
        }
        for &(_, child) in &named_args {
            self.check_bare_arrow_typo(child, position, bound);
        }
    }

    /// WI-618 leaf test: the first binder-looking `Ident` leaf under a minted
    /// arrow that fails to resolve in the current scope — `NotFound` or
    /// `Ambiguous` (an ambiguous data leaf gets no diagnostic elsewhere:
    /// rule-body idents ride as inert data, so silence here would keep the
    /// typo silent). "Binder-looking" = lowercase or `_`-led, the language's
    /// value-binder convention; an UPPERCASE unresolved leaf is deliberately
    /// not a witness — it reads as a sort/type name (e.g. a rule type-var by
    /// convention), and the lambda hint would be wrong advice for what is
    /// then a missing-import/typo'd-sort problem (a pre-existing, broader
    /// silence not specific to arrows). Known false negative, accepted: a
    /// typo whose every binder happens to collide with an in-scope name
    /// (`(nil, cons) -> …`, an op param named like the binder) has no
    /// unresolvable witness and still loads silently — catching it needs
    /// type-level reasoning, not scope lookups.
    ///
    /// Binder forms met under the arrow scope their pattern names via
    /// `bound` (see `check_bare_arrow_typo`). The name `Ident`s at
    /// `pos_args[1]` of converter-minted `field_access`/`dot_apply` nodes
    /// are skipped: a field or method name resolves via its receiver, not in
    /// scope, so it can never witness the typo (the receiver side is still
    /// walked; a user-written call that merely NAMES a functor
    /// `field_access` is not minted and is walked in full).
    fn first_unresolvable_arrow_leaf(
        &self,
        parse_id: TermId,
        bound: &HashSet<String>,
    ) -> Option<String> {
        match self.parsed.terms.get(parse_id) {
            Term::Ident(sym) => {
                let name = self.parsed.symbols.name(*sym);
                let binder_lead = name
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_lowercase() || c == '_');
                if binder_lead
                    && !bound.contains(name)
                    && !matches!(
                        self.kb.symbols.resolve_in_scope(name, self.current_scope.raw()),
                        ResolveResult::Found(_)
                    )
                {
                    return Some(name.to_owned());
                }
                None
            }
            Term::Fn { functor, pos_args, named_args } => {
                let name = self.parsed.symbols.name(*functor);
                // Provenance + arity gate, as in `check_bare_arrow_typo`.
                let minted_binder = binder_form_layout(name)
                    .filter(|_| self.parsed.terms.is_minted(parse_id))
                    .and_then(|(pat_idx, scoped_from)| {
                        pos_args.get(pat_idx).map(|&pat| (pat_idx, scoped_from, pat))
                    });
                if let Some((pat_idx, scoped_from, pat)) = minted_binder {
                    let mut inner = bound.clone();
                    self.pattern_binder_names(pat, &mut inner);
                    for (i, &child) in pos_args.iter().enumerate() {
                        if i == pat_idx {
                            continue; // the pattern binds, it doesn't reference
                        }
                        let scope = if i >= scoped_from { &inner } else { bound };
                        if let Some(w) = self.first_unresolvable_arrow_leaf(child, scope) {
                            return Some(w);
                        }
                    }
                    for &(_, child) in named_args {
                        if let Some(w) = self.first_unresolvable_arrow_leaf(child, &inner) {
                            return Some(w);
                        }
                    }
                    return None;
                }
                let skip_name_slot = matches!(name, "field_access" | "dot_apply")
                    && self.parsed.terms.is_minted(parse_id);
                for (i, &child) in pos_args.iter().enumerate() {
                    if skip_name_slot && i == 1 {
                        continue;
                    }
                    if let Some(w) = self.first_unresolvable_arrow_leaf(child, bound) {
                        return Some(w);
                    }
                }
                for &(_, child) in named_args {
                    if let Some(w) = self.first_unresolvable_arrow_leaf(child, bound) {
                        return Some(w);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// WI-618: read-only mirror of `collect_pattern_names_into` — the bound
    /// variable NAMES of a `pattern_var`/`pattern_tuple`/`pattern_constructor`
    /// parse pattern, without minting binder symbols (this pre-pass must not
    /// disturb the per-site alpha-renaming the load walk performs).
    fn pattern_binder_names(&self, parse_id: TermId, out: &mut HashSet<String>) {
        let Term::Fn { functor, pos_args, named_args } = self.parsed.terms.get(parse_id)
        else { return };
        match self.parsed.symbols.name(*functor) {
            "pattern_var" => {
                if let Some(&first) = pos_args.first() {
                    if let Term::Ident(sym) = self.parsed.terms.get(first) {
                        out.insert(self.parsed.symbols.name(*sym).to_owned());
                    }
                }
            }
            "pattern_tuple" => {
                for &sub in pos_args {
                    self.pattern_binder_names(sub, out);
                }
            }
            "pattern_constructor" => {
                for &sub in pos_args.iter().skip(1) {
                    self.pattern_binder_names(sub, out);
                }
                for &(_, sub) in named_args {
                    self.pattern_binder_names(sub, out);
                }
            }
            _ => {}
        }
    }

    /// Build a let/lambda/match-branch local-name scope frame from the
    /// pattern's bound variable names. Returns the frame to push onto
    /// `local_names_stack`. Empty patterns (wildcard, literal) produce
    /// an empty frame; callers should skip the Push/Pop ops in that
    /// case to avoid no-op stack churn.
    fn build_pattern_scope_frame(&mut self, parse_id: TermId) -> HashMap<String, Symbol> {
        let mut frame: HashMap<String, Symbol> = HashMap::new();
        self.collect_pattern_names_into(parse_id, &mut frame);
        frame
    }

    /// Walk a parse-time pattern term and add each bound variable's
    /// (short_name → KB symbol) entry into `frame`. The KB symbol is
    /// the bare intern of the short name, matching what
    /// `load_pattern_var → reintern` produces for the pattern itself.
    fn collect_pattern_names_into(
        &mut self,
        parse_id: TermId,
        frame: &mut HashMap<String, Symbol>,
    ) {
        // Borrow `parsed.terms` immutably; `kb.intern` borrows kb mutably.
        // Extract the structural data we need first, drop the borrow,
        // then intern.
        let (functor_name, pos_args, named_args) = {
            let t = self.parsed.terms.get(parse_id);
            match t {
                Term::Fn { functor, pos_args, named_args } => {
                    let n = self.parsed.symbols.name(*functor).to_owned();
                    (n, pos_args.clone(), named_args.clone())
                }
                _ => return,
            }
        };
        match functor_name.as_str() {
            "pattern_var" => {
                // WI-550: alpha-rename this binder to a fresh per-site Symbol,
                // keyed by the `pattern_var` parse node (`parse_id`) so
                // `load_pattern_var` later resolves the SAME identity. Extract the
                // owned name first (dropping the `parsed` borrow) before minting.
                let name = pos_args.first().and_then(|&first| {
                    match self.parsed.terms.get(first) {
                        Term::Ident(sym) => Some(self.parsed.symbols.name(*sym).to_owned()),
                        _ => None,
                    }
                });
                if let Some(name) = name {
                    let kb_sym = self.binder_sym(&name, parse_id);
                    frame.insert(name, kb_sym);
                }
            }
            "pattern_tuple" => {
                for sub in pos_args {
                    self.collect_pattern_names_into(sub, frame);
                }
            }
            "pattern_constructor" => {
                // pos_args[0] is the constructor name; the rest are
                // positional sub-patterns. `named_args` carries the
                // `case Foo(field = pat)` form's sub-patterns under
                // their field names — those bind too.
                for sub in pos_args.into_iter().skip(1) {
                    self.collect_pattern_names_into(sub, frame);
                }
                for (_, sub) in named_args {
                    self.collect_pattern_names_into(sub, frame);
                }
            }
            _ => {}
        }
    }

    /// Re-intern a symbol from the parse interner into the KB interner.
    /// Plain intern — no scope-aware resolution. Used for field names,
    /// param names, meta keys, variable names.
    fn reintern(&mut self, sym: Symbol) -> Symbol {
        if let Some(&mapped) = self.sym_map.get(&sym.index()) {
            return mapped;
        }
        let s = self.parsed.symbols.resolve(sym);
        let new_sym = self.kb.intern(s);
        self.sym_map.insert(sym.index(), new_sym);
        new_sym
    }

    /// Human-readable name for the current scope (for error messages).
    fn scope_display_name(&self) -> String {
        match self.kb.get_term(self.current_scope) {
            Term::Fn { functor, .. } => {
                match self.kb.symbols.get(*functor) {
                    SymbolDef::Resolved { short_name, .. } => short_name.clone(),
                    SymbolDef::Unresolved { name } => name.clone(),
                }
            }
            _ => "_unknown".to_owned(),
        }
    }

    /// Extract qualified names from a list of candidate symbols (for error messages).
    fn candidate_names(&self, candidates: &[Symbol]) -> Vec<String> {
        candidates.iter().map(|&sym| {
            match self.kb.symbols.get(sym) {
                SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                SymbolDef::Unresolved { name } => name.clone(),
            }
        }).collect()
    }

    /// WI-369: if `name` (resolved while IGNORING the `internal` filter) names an
    /// `internal` symbol not visible from the current scope, return it. Lets the
    /// resolvers tell a forbidden cross-scope reference to an internal name apart
    /// from a genuinely-unknown name, so they can emit a precise
    /// `ForbiddenInternalAccess` instead of a bare `UnresolvedName`.
    fn hidden_internal(&self, name: &str) -> Option<Symbol> {
        let scope = self.current_scope.raw();
        if let ResolveResult::Found(sym) =
            self.kb.symbols.resolve_in_scope_ignoring_internal(name, scope)
        {
            if !self.kb.symbols.internal_visible_from(sym, scope) {
                return Some(sym);
            }
        }
        None
    }

    /// WI-369: whether a `by_qualified_name` hit is visible from the current
    /// scope — the qualified path bypasses `resolve_in_scope`'s `internal`
    /// filter, so it must apply the same visibility gate explicitly.
    fn qualified_visible(&self, sym: Symbol) -> bool {
        self.kb.symbols.internal_visible_from(sym, self.current_scope.raw())
    }

    /// WI-369: record a `ForbiddenInternalAccess` for `sym` (referenced as
    /// `name` at `span`) and return a bare interned symbol so the term stays
    /// well-formed; the load fails on the recorded (load-blocking) error.
    /// `declared_in` is derived from the symbol's qualified name.
    fn push_forbidden_internal(&mut self, sym: Symbol, name: &str, span: Span) -> Symbol {
        let declared_in = match self.kb.symbols.get(sym) {
            SymbolDef::Resolved { qualified_name, .. } => qualified_name
                .rsplit_once('.')
                .map(|(p, _)| p.to_owned())
                .unwrap_or_else(|| qualified_name.clone()),
            SymbolDef::Unresolved { name } => name.clone(),
        };
        self.errors.push(LoadError::ForbiddenInternalAccess {
            name: name.to_owned(),
            declared_in,
            scope_name: self.scope_display_name(),
            span,
        });
        self.kb.symbols.intern(name)
    }

    /// WI-369: NotFound-arm helper for the resolvers — if `name` is a forbidden
    /// cross-scope reference to an `internal` symbol, record a
    /// `ForbiddenInternalAccess` (load-blocking) and return a bare interned
    /// symbol so the term stays well-formed. Returns `None` when `name` is not a
    /// hidden-internal reference (the caller proceeds with its normal fallback).
    fn forbid_if_internal(&mut self, name: &str, span: Span) -> Option<Symbol> {
        let sym = self.hidden_internal(name)?;
        Some(self.push_forbidden_internal(sym, name, span))
    }

    /// Scope-aware symbol resolution for functors and type/sort references.
    /// If resolution finds a defined symbol, returns it; otherwise falls
    /// back to plain intern (term-level functors may be undefined data names).
    /// Ambiguous matches are still hard errors.
    ///
    /// Consults the let/lambda/match-branch local-name scope stack
    /// first. A pattern-bound name in scope shadows any same-short-name
    /// rule / op / param / etc., so a body's reference to a let-bound
    /// `y` resolves to the binder, not an unrelated definition elsewhere.
    fn remap_symbol(&mut self, sym: Symbol) -> Symbol {
        let name = self.parsed.symbols.name(sym).to_owned();
        self.remap_name_str(&name)
    }

    /// [`remap_symbol`] on a raw name string. WI-443 needs the string form:
    /// the dot member of an identifier-receiver call exists only as a
    /// segment of the flattened functor name, never as a parse `Symbol`.
    /// (Distinct from `remap_name`, which takes the structured parse `Name`.)
    fn remap_name_str(&mut self, name: &str) -> Symbol {
        let sym = self.remap_name_str_inner(name);
        // WI-529: an operation body is value/eval context, so the boolean operators
        // `not`/`or` mean the dispatched Bool VALUE ops, NEVER the resolver primitives
        // (`reflect.not` NAF / `kernel.or` disjunction — neither has an eval builtin).
        // Redirect AFTER resolution so it catches the name however `not`/`or` resolved:
        // the implicit fallback OR an explicit `import anthill.reflect.{not}` (which
        // would otherwise shadow the routing via a `Found` hit). A user's own `not`/`or`
        // operation resolves to a different symbol and is left untouched. No-op outside
        // an op body.
        if self.in_op_body_value {
            return self.redirect_op_body_boolean(sym);
        }
        sym
    }

    /// WI-529: in op-body value context, map a resolved resolver-primitive symbol to
    /// its dispatched Bool value-op counterpart (`reflect.not` → `Bool.not`,
    /// `kernel.or` → `Bool.or`). Returns `sym` unchanged when it is neither primitive
    /// (or when the Bool target is not loaded). `and`/`neg` need no entry — they have no
    /// resolver primitive and already route to `Bool.and` / `Numeric.neg` everywhere.
    fn redirect_op_body_boolean(&self, sym: Symbol) -> Symbol {
        let map = |from: &str, to: &str| -> Option<Symbol> {
            if self.kb.symbols.by_qualified_name.get(from).copied() != Some(sym) {
                return None;
            }
            self.kb.symbols.by_qualified_name.get(to).copied()
        };
        map("anthill.reflect.not", "anthill.prelude.Bool.not")
            .or_else(|| map("anthill.kernel.or", "anthill.prelude.Bool.or"))
            .unwrap_or(sym)
    }

    /// `remap_name_str` without the op-body boolean redirect (the resolution itself).
    fn remap_name_str_inner(&mut self, name: &str) -> Symbol {
        if let Some(local) = self.lookup_local_name(name) {
            return local;
        }
        let scope = self.current_scope.raw();
        match self.kb.symbols.resolve_in_scope(name, scope) {
            ResolveResult::Found(resolved) => resolved,
            ResolveResult::Ambiguous(candidates) => {
                self.errors.push(LoadError::AmbiguousSymbol {
                    name: name.to_owned(),
                    candidates: self.candidate_names(&candidates),
                    span: Span::default(),
                    scope_name: self.scope_display_name(),
                });
                self.kb.symbols.intern(name)
            }
            ResolveResult::NotFound => {
                // Dotted name: try segment-aware resolution. Resolve the
                // head segment in scope (Map → anthill.prelude.Map), then
                // append the trailing segments to its qualified path and
                // look the result up directly. Covers the dotted-call form
                // `Map.empty()` and proposal-035 form (3) `Map[...].empty()`,
                // both of which produce a single joined Symbol "Map.empty"
                // that doesn't appear in any scope's locals/imports.
                if let Some((head, tail)) = name.split_once('.') {
                    if let ResolveResult::Found(head_sym) =
                        self.kb.symbols.resolve_in_scope(head, scope)
                    {
                        let head_qualified = match self.kb.symbols.get(head_sym) {
                            SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                            SymbolDef::Unresolved { name } => name.clone(),
                        };
                        let probe = format!("{}.{}", head_qualified, tail);
                        if let Some(&q_sym) = self.kb.symbols.by_qualified_name.get(&probe) {
                            // WI-369: the qualified path bypasses the `internal`
                            // filter. Return the hit if visible here; otherwise
                            // it is a forbidden cross-scope internal reference.
                            if self.qualified_visible(q_sym) {
                                return q_sym;
                            }
                            return self.push_forbidden_internal(q_sym, name, Span::default());
                        }
                    }
                }
                // WI-040 / WI-521: reserved kernel desugaring vocab (synthesized
                // `match_expr` / `field_access` / `ListLiteral` / …) and the
                // implicit PRELUDE (`cons` / `some` / `eq` / `add` / `not` / …)
                // resolve directly to their qualified home, replacing the old
                // `_global` imports. This is a FALLBACK (we are already past scope
                // resolution), so a user-written same-spelling name has won
                // already; these names only catch a reference no scope defines.
                if let Some(qn) = implicit_qualified(name) {
                    if let Some(&sym) = self.kb.symbols.by_qualified_name.get(qn) {
                        return sym;
                    }
                }
                // WI-369: distinguish a forbidden cross-scope reference to an
                // `internal` name from a genuinely-unknown one before falling back.
                if let Some(sym) = self.forbid_if_internal(name, Span::default()) {
                    return sym;
                }
                // WI-476: name not resolvable in the local environment. A
                // functor / identifier that names nothing in scope is interned as
                // a bare symbol (a data name, or a genuinely-unknown functor the
                // typer then rejects as an unknown operation). This replaced the
                // global short-name fallback (`resolve_by_short_name`), which
                // silently rescued such names by scanning every qualified name in
                // the KB and so masked missing imports — see the model note in
                // `resolve_in_scope`'s callers.
                self.kb.symbols.intern(name)
            }
        }
    }

    /// Strict scope-aware symbol resolution: errors on unresolved names.
    /// Used for positions where a symbol *must* be defined (functor names,
    /// explicit references). Unlike `remap_symbol`, does not silently intern.
    fn remap_symbol_strict(&mut self, sym: Symbol) -> Symbol {
        let name = self.parsed.symbols.name(sym);
        let scope = self.current_scope.raw();
        match self.kb.symbols.resolve_in_scope(name, scope) {
            ResolveResult::Found(resolved) => resolved,
            ResolveResult::Ambiguous(candidates) => {
                self.errors.push(LoadError::AmbiguousSymbol {
                    name: name.to_owned(),
                    candidates: self.candidate_names(&candidates),
                    span: Span::default(),
                    scope_name: self.scope_display_name(),
                });
                self.kb.symbols.intern(name)
            }
            ResolveResult::NotFound => {
                // WI-369: a forbidden cross-scope `internal` reference gets a
                // precise diagnostic rather than a misleading "unresolved name".
                if let Some(sym) = self.forbid_if_internal(name, Span::default()) {
                    return sym;
                }
                let sym = self.kb.symbols.intern(name);
                self.errors.push(LoadError::UnresolvedName {
                    name: name.to_owned(),
                    span: Span::default(),
                    scope_name: self.scope_display_name(),
                });
                sym
            }
        }
    }

    /// Scope-aware name resolution for multi-segment names.
    fn remap_name(&mut self, name: &Name) -> Symbol {
        let lookup_name = if name.segments.len() == 1 {
            self.parsed.symbols.name(name.segments[0]).to_owned()
        } else {
            join_segments(&self.parsed.symbols, &name.segments)
        };
        let scope = self.current_scope.raw();
        match self.kb.symbols.resolve_in_scope(&lookup_name, scope) {
            ResolveResult::Found(resolved) => resolved,
            ResolveResult::Ambiguous(candidates) => {
                self.errors.push(LoadError::AmbiguousSymbol {
                    name: lookup_name.clone(),
                    candidates: self.candidate_names(&candidates),
                    span: name.span,
                    scope_name: self.scope_display_name(),
                });
                self.kb.symbols.intern(&lookup_name)
            }
            ResolveResult::NotFound => {
                // For multi-segment names, try qualified name lookup
                // (the name might be defined via dotted declaration in
                // an intermediate namespace not yet in our scope chain)
                if name.segments.len() > 1 {
                    if let Some(&sym) = self.kb.symbols.by_qualified_name.get(&lookup_name) {
                        // WI-369: qualified path bypasses the `internal` filter.
                        if self.qualified_visible(sym) {
                            return sym;
                        }
                        return self.push_forbidden_internal(sym, &lookup_name, name.span);
                    }
                }
                // WI-369: precise diagnostic for a forbidden cross-scope
                // `internal` reference before the unresolved-name fallbacks.
                if let Some(sym) = self.forbid_if_internal(&lookup_name, name.span) {
                    return sym;
                }
                let sym = self.kb.symbols.intern(&lookup_name);
                // WI-440: inside a `-E` absence label, an unresolved name means
                // the declared constraint is VACUOUS (nothing would ever match
                // the place) — fail loudly instead of warning and proceeding.
                if self.in_effect_absence {
                    self.errors.push(LoadError::UnresolvedEffectPlace {
                        name: lookup_name,
                    });
                } else if self.in_type_position
                    && name.segments.len() > 1
                    && self
                        .parsed
                        .symbols
                        .name(*name.segments.last().unwrap())
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_uppercase())
                {
                    // WI-429: an unresolvable Capitalized DOTTED name in type
                    // position is a hard error — every legitimate spelling
                    // (value projection, type-receiver projection, qualified
                    // child / sort ref) was already classified or resolved
                    // before reaching this arm, so what's left is a typo that
                    // would mint a degenerate nominal sort. A lowercase-member
                    // dotted name (a value place like `Modify[result.a]`)
                    // keeps the advisory path.
                    self.errors.push(LoadError::UnresolvedTypeName {
                        name: lookup_name,
                        span: name.span,
                        scope_name: self.scope_display_name(),
                    });
                } else {
                    self.errors.push(LoadError::UnresolvedName {
                        name: lookup_name,
                        span: name.span,
                        scope_name: self.scope_display_name(),
                    });
                }
                sym
            }
        }
    }

    /// Record a stored term's source span on the KB's
    /// `term_spans` / `functor_spans` side-tables — typing.rs and
    /// other passes read these for error-reporting spans.
    /// First-write-wins on both keys mirrors the legacy
    /// `the legacy occurrence by-term index/rules_by_functor.first()` semantics.
    fn create_occurrence(&mut self, parse_id: TermId, kb_id: TermId) {
        let span = self.parsed.terms.span(parse_id);
        let source_span = SourceSpan::from_span(self.source_id, span);
        self.kb.term_spans.entry(kb_id).or_insert(source_span);
        if let Term::Fn { functor, .. } = self.kb.terms.get(kb_id) {
            let functor = *functor;
            self.kb.functor_spans.entry(functor).or_insert(source_span);
        }
    }

    /// True iff `sym` names the stdlib `List` sort. Shared by [`Self::is_list_sort_ref`]
    /// (the whole-type check) and [`Self::find_list_element_type`] (the base check).
    fn is_list_sort_sym(kb: &KnowledgeBase, sym: Symbol) -> bool {
        let n = kb.qualified_name_of(sym);
        n == "anthill.prelude.List" || n == "anthill.prelude.List.List"
    }

    /// True iff `ty` is the `List` sort. WI-361 dual-form: the term-backed bare
    /// sort `Ref(List)` or the deep `sort_ref(name: Ref(List))`.
    fn is_list_sort_ref(kb: &KnowledgeBase, ty: TermId) -> bool {
        extract_sort_ref_sym(kb, &TermIdView(ty)).is_some_and(|s| Self::is_list_sort_sym(kb, s))
    }

    /// `Some(element_hint)` if `ty` is List-shaped, else `None` — outer
    /// `Some` signals "desugar ListLiteral here" (WI-007), inner `Option`
    /// is the element-type hint to propagate. Recurses through wrappers like
    /// `Option[T = List[T = X]]`: the literal is the wrapper's PAYLOAD —
    /// desugared here, then wrapped in `some(…)` by `wrap_bare_option_value`
    /// (WI-408).
    fn find_list_element_type(kb: &KnowledgeBase, ty: TermId) -> Option<Option<TermId>> {
        if Self::is_list_sort_ref(kb, ty) { return Some(None); }
        // WI-361: a parameterized `List[T=X]` is deep `parameterized(base: List,
        // bindings)` or term-backed `Fn{List, named}` — read base + bindings
        // form-agnostically via `extract_type`.
        let TypeExtractor::Parameterized { base, bindings } = extract_type(kb, &TermIdView(ty)) else {
            return None;
        };
        if Self::is_list_sort_sym(kb, base) {
            // The element hint is the `T` binding's value — already materialized in
            // `bindings`, so read it here rather than re-walking via extract_type_param.
            let hint = bindings
                .iter()
                .find(|(p, _)| kb.resolve_sym(*p) == "T")
                .and_then(|(_, v)| match v {
                    Value::Term { id: t, .. } => Some(*t),
                    _ => None,
                });
            return Some(hint);
        }

        for (_param, value) in &bindings {
            if let Value::Term { id: v, .. } = value {
                if let Some(inner) = Self::find_list_element_type(kb, *v) {
                    return Some(inner);
                }
            }
        }
        None
    }

    /// WI-408 (loader leg of the some-insertion pass): a bare value supplied
    /// for an `Option[…]`-typed entity field is wrapped in `some(…)` at
    /// conversion time, so term-world content asserted BEFORE the typing pass
    /// — on-disk facts, rule-body entity atoms — carries properly
    /// Option-typed slots (the on-disk format may still say `depends_on:
    /// [...]`; it loads as `some([...])` and round-trips explicit). Skipped
    /// for: a non-Option (or absent/denoted) field hint; a variable (it binds
    /// the WHOLE Option value, `some(…)`/`none()` alike); a value already
    /// headed by `Option.some`/`Option.none`. A constructor PATTERN in an
    /// Option slot (`depends_on: cons(…)` in a rule body) wraps like a value
    /// — the pattern then matches the wrapped facts, preserving rule meaning.
    fn wrap_bare_option_value(&mut self, term: TermId, expected: Option<TermId>) -> TermId {
        let Some(exp) = expected else { return term };
        if !super::typing::is_option_type(self.kb, &TermIdView(exp)) {
            return term;
        }
        let head_functor = match self.kb.get_term(term) {
            Term::Var(_) => return term,
            Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => Some(*functor),
            _ => None, // Const literal — always a bare payload
        };
        if let Some(f) = head_functor {
            let qn = self.kb.qualified_name_of(f);
            if qn == "anthill.prelude.Option.some" || qn == "anthill.prelude.Option.none" {
                return term;
            }
        }
        build_some(self.kb, term)
    }

    /// Convert a parse-time TermId to a KB TermId, re-allocating into the hash-consed store.
    fn convert_term(&mut self, parse_id: TermId) -> TermId {
        self.convert_term_with_expected(parse_id, None)
    }

    /// WI-716: convert a constructor ARGUMENT (a field value) under the value/pattern
    /// context. A reflect `Term`-typed field holds a QUOTED pattern, not a value, so an
    /// omitted optional inside it must var-fill ("match anything"), never default to
    /// `none()` — otherwise a stored query pattern like `FactHolds(pattern: E(id: ?x))`
    /// would silently match only `E`s whose optional field is `none()`. Clear
    /// `in_value_position` for that field's subtree; every other field converts under
    /// the ambient context.
    fn convert_arg_value(&mut self, parse_id: TermId, expected: Option<TermId>) -> TermId {
        let quoted = expected
            .is_some_and(|e| super::typing::is_reflect_term_type(self.kb, &TermIdView(e)));
        if quoted && self.in_value_position {
            self.in_value_position = false;
            let r = self.convert_term_with_expected(parse_id, expected);
            self.in_value_position = true;
            r
        } else {
            self.convert_term_with_expected(parse_id, expected)
        }
    }

    /// Like `convert_term` but takes an optional expected-type hint that drives
    /// context-aware ListLiteral desugaring (WI-007). When `expected` is a
    /// `List`-shaped type, `ListLiteral` is rewritten to `cons/nil`; otherwise
    /// it stays in the KB as `ListLiteral` for downstream consumers.
    ///
    /// WI-710: maintains `term_depth` (see the field) across the WHOLE conversion —
    /// every recursive child goes through here, so the inner fn can tell a top-level
    /// term (an instance claim) from a nested one (a type). A wrapper rather than
    /// bookkeeping inside the body, which has several early returns that would each
    /// have to restore the counter.
    fn convert_term_with_expected(&mut self, parse_id: TermId, expected: Option<TermId>) -> TermId {
        let saved = self.term_depth;
        self.term_depth = saved + 1;
        let converted = self.convert_term_inner(parse_id, expected);
        self.term_depth = saved;
        converted
    }

    fn convert_term_inner(&mut self, parse_id: TermId, expected: Option<TermId>) -> TermId {
        if let Some(&mapped) = self.term_map.get(&parse_id.raw()) {
            return mapped;
        }

        let parse_term = self.parsed.terms.get(parse_id).clone();
        let kb_term = match parse_term {
            Term::Const(lit) => Term::Const(lit),
            Term::Var(Var::Global(vid)) => {
                let kb_vid = if let Some(&mapped) = self.var_map.get(&vid.raw()) {
                    mapped
                } else {
                    let name = self.reintern(vid.name());
                    let new_vid = self.kb.fresh_var(name);
                    self.var_map.insert(vid.raw(), new_vid);
                    new_vid
                };
                Term::Var(Var::Global(kb_vid))
            }
            Term::Var(Var::DeBruijn(n)) => Term::Var(Var::DeBruijn(n)),
            Term::Var(Var::Rigid(_)) => {
                unreachable!("Var::Rigid in stored parse term")
            }
            Term::Fn { functor, pos_args, named_args } => {
                // WI-582: a `typed_var(?x, type: T)` marker — the converter's
                // lowering of a `?x: T` rule-pattern arg. STRIP it: convert the
                // inner variable so the head term stays structurally the bare
                // `?x` (the discrimination tree indexes a typed head identically
                // to the untyped one — carrier-neutral, M1), resolve the declared
                // type to a bound term, and RECORD (var, bound) so `load_rule`
                // installs it as a per-variable `Type` constraint keyed by the
                // variable's DeBruijn index. A `typed_var` outside a rule head is
                // a misuse (annotation on a non-pattern variable) — report loudly
                // rather than silently dropping the bound.
                if self.parsed.symbols.name(functor) == "typed_var"
                    && pos_args.len() == 1
                    && named_args.iter().any(|(s, _)| self.parsed.symbols.name(*s) == "type")
                {
                    let var_kb = self.convert_term(pos_args[0]);
                    let ty_expr_opt = self.read_parse_aux(parse_id, "type", |aux| match aux {
                        crate::parse::ir::ParseAux::TypeExpr(ty) => Some(ty.clone()),
                        _ => None,
                    });
                    let bound = match ty_expr_opt {
                        // WI-582 `[T]`-form: `?x: T` where `T` is a head-introduced
                        // type-var. Its effective bound is the one its `:- Spec[T]`
                        // guard gave it (recorded in `rule_tvar_bounds` by
                        // `load_rule`), not `T` itself — `T` has no nominal sort and
                        // would never fire. The guard goal is dropped (folded here).
                        Some(crate::parse::ir::TypeExpr::Simple(ref n))
                            if n.segments.len() == 1
                                && self
                                    .rule_tvar_bounds
                                    .contains_key(self.parsed.symbols.name(n.segments[0])) =>
                        {
                            let nm = self.parsed.symbols.name(n.segments[0]);
                            *self.rule_tvar_bounds.get(nm).unwrap()
                        }
                        Some(ty_expr) => {
                            let value = self.type_expr_to_value(&ty_expr);
                            match node_occurrence::value_to_term(&mut self.kb, &value) {
                                Ok(t) => t,
                                Err(e) => {
                                    // Loud over silent (consistent with the `None`
                                    // arm below): a non-term-representable bound is
                                    // a load error, not a silent `Bottom` that makes
                                    // the rule never fire.
                                    self.errors.push(LoadError::Other {
                                        message: format!(
                                            "WI-582: typed rule pattern bound is not \
                                             term-representable: {e:?}"
                                        ),
                                    });
                                    self.kb.alloc(Term::Bottom)
                                }
                            }
                        }
                        None => {
                            self.errors.push(LoadError::Other {
                                message: "WI-582: typed rule pattern `?x: T` is missing its type"
                                    .to_string(),
                            });
                            self.kb.alloc(Term::Bottom)
                        }
                    };
                    // VarId is Copy — read it out so the immutable `kb` borrow is
                    // released before the mutable push.
                    let vid_opt = match self.kb.get_term(var_kb) {
                        Term::Var(Var::Global(vid)) => Some(*vid),
                        _ => None,
                    };
                    if !self.in_rule_head {
                        self.errors.push(LoadError::Other {
                            message: "WI-582: a variable type annotation (`?x: T`) is only \
                                      meaningful in a rule head pattern"
                                .to_string(),
                        });
                    } else if let Some(vid) = vid_opt {
                        // WI-582: a variable's type bound is declared ONCE. A
                        // conflicting re-annotation (`?x: A` … `?x: B`) is a loud
                        // load error (ticket acceptance); an identical re-annotation
                        // is idempotent (bounds are hash-consed → same TermId).
                        match self.rule_head_type_bounds.iter().find(|(v, _)| *v == vid) {
                            Some((_, prev)) if *prev != bound => {
                                self.errors.push(LoadError::Other {
                                    message: "WI-582: a rule variable has conflicting type \
                                              annotations; a variable's type bound must be \
                                              declared once"
                                        .to_string(),
                                });
                            }
                            Some(_) => {} // identical re-annotation: idempotent
                            None => self.rule_head_type_bounds.push((vid, bound)),
                        }
                    } else {
                        self.errors.push(LoadError::Other {
                            message: "WI-582: a typed rule pattern annotation must be on a \
                                      variable (`?x: T`)"
                                .to_string(),
                        });
                    }
                    self.term_map.insert(parse_id.raw(), var_kb);
                    return var_kb;
                }
                // WI-278: re-encode a *converter-emitted* parse
                // `dot_apply(receiver, Ident(name), ...positional)` + named
                // call-args into the canonical reflect form
                // `dot_apply(receiver, name: Ref, args: List[ApplyArg])`. The
                // top-level wrapper matches the occurrence path (convert_expr's
                // LoadBuildFrame::DotApply); the children differ on purpose —
                // here they stay bare terms (convert_term-recursed: Const / Var
                // / Fn), since term consumers (smt-gen, the [simp] engine) read
                // raw terms, whereas convert_expr wraps them as reflect Expr
                // nodes. Do NOT "unify" the two paths. Without this, the generic
                // Fn conversion below leaves receiver/name *positional* and
                // stuffs a fresh var into the dot_apply entity's `args` field —
                // a malformed dot_apply no consumer can read (rule bodies reach
                // dot_apply here via load_rule → convert_term, not convert_expr).
                //
                // `dot_apply` is NOT a reserved name, and convert_term also
                // sees rule/fact/query terms the user typed. The arity +
                // `Ident`-name guard matches only the converter form: a
                // user-written `dot_apply(?x)` / `dot_apply()` / a user
                // `entity dot_apply` (named-arg construction) falls through to
                // generic conversion — and MUST, else `pos_args[1]` would panic
                // on < 2 positional args.
                if self.parsed.symbols.name(functor) == "dot_apply"
                    && pos_args.len() >= 2
                    && matches!(self.parsed.terms.get(pos_args[1]), Term::Ident(_))
                {
                    let receiver = self.convert_term(pos_args[0]);
                    // The name is metadata at pos_args[1] (an Ident) — resolve
                    // to a Ref, don't recurse it as a child.
                    let name_term = self.parsed.terms.get(pos_args[1]).clone();
                    let name_ref = if let Term::Ident(sym) = name_term {
                        let kb_sym = self.remap_symbol(sym);
                        self.kb.alloc(Term::Ref(kb_sym))
                    } else {
                        self.convert_term(pos_args[1])
                    };
                    let mut arg_terms: SmallVec<[TermId; 4]> = SmallVec::new();
                    for &pid in &pos_args[2..] {
                        let value = self.convert_term(pid);
                        let none = build_none(self.kb);
                        arg_terms.push(self.mk_apply_arg(none, value));
                    }
                    for &(sym, pid) in named_args.iter() {
                        let value = self.convert_term(pid);
                        let reinterned = self.reintern(sym);
                        let arg_name = self.kb.alloc(Term::Ref(reinterned));
                        let some_name = build_some(self.kb, arg_name);
                        arg_terms.push(self.mk_apply_arg(some_name, value));
                    }
                    let args_list = build_list(self.kb, &arg_terms);
                    let (dot, k_receiver, k_name, k_args) = {
                        let s = &self.expr_syms;
                        (s.dot_apply, s.k_receiver, s.k_name, s.k_args)
                    };
                    let kb_id = self.kb.alloc(Term::Fn {
                        functor: dot,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::from_slice(&[
                            (k_receiver, receiver),
                            (k_name, name_ref),
                            (k_args, args_list),
                        ]),
                    });
                    self.term_map.insert(parse_id.raw(), kb_id);
                    return kb_id;
                }

                let new_functor = self.remap_symbol(functor);

                // WI-007 context-aware ListLiteral desugaring: only rewrite
                // `ListLiteral → cons/nil` when the surrounding field type is
                // List-shaped (recursing through wrappers like
                // `Option[T = List[T = X]]`). The inner `Option<TermId>` is
                // the recursive element-type hint, so nested
                // `[[...], ...]` for `List[T = List[T = X]]` propagates.
                let elem_hint = expected.and_then(|e| Self::find_list_element_type(self.kb, e));
                if self.kb.qualified_name_of(new_functor) == "anthill.reflect.ListLiteral"
                    && elem_hint.is_some()
                {
                    let elem_expected = elem_hint.flatten();
                    let items: Vec<TermId> = pos_args.iter()
                        // WI-716: route through `convert_arg_value` so a `List[Term]`
                        // element (a quoted pattern) clears the value flag like a bare
                        // `Term` field — its omitted optionals stay vars, not `none()`.
                        .map(|&id| self.convert_arg_value(id, elem_expected))
                        .collect();
                    let kb_id = build_list(self.kb, &items);
                    self.term_map.insert(parse_id.raw(), kb_id);
                    if let Some(desc_texts) = self.parsed.terms.descriptions.get(&parse_id) {
                        let desc_texts = desc_texts.clone();
                        for desc_text in &desc_texts {
                            self.emit_desc_fact(kb_id, desc_text, self.current_scope);
                        }
                    }
                    return kb_id;
                }

                // WI-408: an explicit `some(payload)` under an `Option[…]`-typed
                // slot threads the PEELED element type into its payload —
                // `some`'s own declared field type is just the type-param `T`,
                // so without this a `depends_on: some(["WI-1"])` payload literal
                // would lose the `List[String]` hint and never desugar.
                let is_some_ctor =
                    self.kb.qualified_name_of(new_functor) == "anthill.prelude.Option.some";
                let some_payload_hint: Option<TermId> = if is_some_ctor {
                    expected
                        .filter(|e| super::typing::is_option_type(self.kb, &TermIdView(*e)))
                        .and_then(|e| {
                            super::typing::extract_type_param(self.kb, &TermIdView(e), "T")
                        })
                        // A denoted/occurrence (`Value::Node`) payload type is no
                        // literal-typing hint — narrow to the ground `TermId` only.
                        .and_then(|v| match v {
                            Value::Term { id: t, .. } => Some(t),
                            _ => None,
                        })
                } else {
                    None
                };
                let mut new_pos: SmallVec<[TermId; 4]> = pos_args
                    .iter()
                    .enumerate()
                    .map(|(i, &id)| {
                        // WI-342: field types are carrier-agnostic; the
                        // conversion hint only wants a ground `TermId` (a
                        // denoted-bearing field is no literal-typing hint → None).
                        let exp = some_payload_hint.or_else(|| {
                            self.kb.entity_field_types(new_functor)
                                .and_then(|ft| ft.get(i).and_then(|(_, t)| match t {
                                    Value::Term { id: t, .. } => Some(*t),
                                    _ => None,
                                }))
                        });
                        let converted = self.convert_arg_value(id, exp);
                        self.wrap_bare_option_value(converted, exp)
                    })
                    .collect();
                // WI-271: skip parse-only ParseAux children (let_expr's
                // `type_name`, apply's `type_args`) — they are read
                // directly at the LoadBuildFrame::LetExpr /
                // ApplyOrConstructor build sites via
                // `read_parse_type_annotation` /
                // `read_parse_call_type_args`. Routing them through
                // convert_term_with_expected would hit the unreachable
                // ParseAux arm below.
                // Pre-collect the non-ParseAux args so the closure
                // body's `self`-mut calls don't re-borrow during
                // iteration.
                // WI-366 B1: keep a written effect-row binding value
                // (`ParseAux::TypeExpr(EffectRow)`, e.g. `fact Spec[E = {}]`) —
                // unlike the let/apply build-site ParseAux payloads, it is a real
                // term-position binding value the ParseAux arm lowers in place.
                let visible_named: SmallVec<[(Symbol, TermId); 2]> = named_args
                    .iter()
                    .filter(|&&(_, id)| !self.is_parse_aux(id) || self.is_effect_row_aux(id))
                    .copied()
                    .collect();
                let mut new_named: SmallVec<[(Symbol, TermId); 2]> = visible_named
                    .into_iter()
                    .map(|(sym, id)| {
                        let new_sym = self.reintern(sym);
                        // WI-408: `some(value: x)` payload takes the peeled hint
                        // (see `some_payload_hint` above the positional loop).
                        let exp = some_payload_hint.or_else(|| {
                            self.kb.entity_field_types(new_functor)
                                .and_then(|ft| ft.iter().find(|(s, _)| *s == new_sym).and_then(|(_, t)| match t {
                                    Value::Term { id: t, .. } => Some(*t),
                                    _ => None,
                                }))
                        });
                        let converted = self.convert_arg_value(id, exp);
                        (new_sym, self.wrap_bare_option_value(converted, exp))
                    })
                    .collect();

                // WI-408: canonicalize a source-written positional `some(x)` to
                // the NAMED form `some(value: x)` — the one in-KB term shape for
                // `some`. The loader's coercion wrap (`build_some`) and the
                // CLI's value→term reflection both emit the named form;
                // term-world unification does not bridge positional↔named, so
                // without this a hand-written `some(...)` rule pattern would
                // never match a wrapped or persisted fact.
                if is_some_ctor && new_pos.len() == 1 && new_named.is_empty() {
                    let value_sym = self.kb.intern("value");
                    new_named.push((value_sym, new_pos.pop().expect("len checked")));
                }

                // WI-433: DESUGAR positional constructor args to NAMED. Positional
                // and named constructor terms must share ONE in-KB shape — a stored
                // fact's named args (sorted by field) never unify with a positional
                // pattern via the discrim tree, so a positional `Verified(?)`
                // pattern silently NEVER matched the named `Verified(at: …)` facts.
                // "Positional application is sugar for names" (kernel spec §5.2;
                // generalizes the `some(x)` case just above). Positional args fill
                // the declared fields NOT already given by name, in declaration
                // order (matching the materializer's rank-among-not-named read, so
                // `pair2(a: 10, 20)` fills `b` and `pair2(1, b: 2)` fills `a`).
                // More positional args than unfilled fields is a loud error (the
                // loud-error principle — never a silent never-match). EXCLUDED: a
                // non-entity functor (tuple / builtin / generic application — no
                // declared fields), and the `anthill.reflect.*` Expr meta-ctors
                // (`ho_apply` / `match_expr` / `if_expr` / …) whose positional shape
                // is the reflect encoding, not user named-field application.
                if !new_pos.is_empty() {
                    let named_syms: SmallVec<[Symbol; 2]> =
                        new_named.iter().map(|(s, _)| *s).collect();
                    match self.kb.positional_to_named_plan(new_functor, &named_syms, new_pos.len()) {
                        PositionalPlan::Skip => {}
                        PositionalPlan::Assign(fields) => {
                            for (i, pos_val) in new_pos.drain(..).enumerate() {
                                new_named.push((fields[i], pos_val));
                            }
                        }
                        PositionalPlan::OverArity { declared, unfilled } => {
                            let fields = declared
                                .iter()
                                .map(|s| self.kb.resolve_sym(*s).to_string())
                                .collect::<Vec<_>>()
                                .join(", ");
                            self.errors.push(LoadError::Other {
                                message: format!(
                                    "constructor '{}' given {} positional argument(s) but has {} unfilled field(s) (declares: {})",
                                    self.kb.resolve_sym(new_functor),
                                    new_pos.len(),
                                    unfilled,
                                    fields,
                                ),
                            });
                        }
                    }
                }

                // Expand partial named args: fill missing entity fields so every
                // fact/pattern of a functor presents the same named slots (the
                // discrim tree matches structurally). Positional args also count as
                // "provided" — `ToolPasses("x")` covers `tool` via pos_args[0], so it
                // isn't re-stuffed with a fresh var that would shadow the positional.
                //
                // WI-716: the FILLER depends on VALUE vs PATTERN position. In a
                // value position (`self.in_value_position` — a fact head or an
                // entity-deriving rule head) an absent OPTIONAL field means
                // `none()`, not a var: a var makes the produced entity
                // `forall v. E(field: v)`, which unsoundly unifies a `some(?)`
                // query. In a query/rule-body PATTERN (and for an absent REQUIRED
                // field) the var-fill stays — "matches anything". A `none()` value
                // still unifies a pattern's var (so `E(id: ?)` finds it) but
                // correctly fails `field: some(?)`.
                if let Some(all_fields) = self.kb.entity_field_names(new_functor) {
                    let all_fields = all_fields.to_vec(); // borrow-safe copy
                    // Field symbols whose declared type is `Option[..]` — computed only
                    // in a value position; patterns keep the uniform var-fill.
                    let optional_fields: HashSet<Symbol> = if self.in_value_position {
                        let fts: Vec<(Symbol, crate::eval::value::Value)> = self
                            .kb
                            .entity_field_types(new_functor)
                            .map(|s| s.to_vec())
                            .unwrap_or_default();
                        fts.iter()
                            .filter(|(_, ty)| crate::kb::typing::is_option_type(&*self.kb, ty))
                            .map(|(s, _)| *s)
                            .collect()
                    } else {
                        HashSet::new()
                    };
                    if new_named.len() + new_pos.len() < all_fields.len() {
                        let mut provided: HashSet<Symbol> = new_named
                            .iter().map(|(s, _)| *s).collect();
                        for (i, &field_sym) in all_fields.iter().enumerate() {
                            if i < new_pos.len() {
                                provided.insert(field_sym);
                            }
                        }
                        for &field_sym in &all_fields {
                            if !provided.contains(&field_sym) {
                                let fill = if optional_fields.contains(&field_sym) {
                                    // WI-716: absent optional in a value position -> none()
                                    let none_sym =
                                        self.kb.resolve_symbol("anthill.prelude.Option.none");
                                    self.kb.alloc(Term::Fn {
                                        functor: none_sym,
                                        pos_args: SmallVec::new(),
                                        named_args: SmallVec::new(),
                                    })
                                } else {
                                    let fresh = self.kb.fresh_var(field_sym);
                                    self.kb.alloc(Term::Var(Var::Global(fresh)))
                                };
                                new_named.push((field_sym, fill));
                            }
                        }
                    }
                    let order: HashMap<Symbol, usize> = all_fields.iter().enumerate()
                        .map(|(i, &s)| (s, i)).collect();
                    new_named.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
                }

                // WI-710: a NESTED sort-headed term is a parameterized TYPE — the
                // `Cell[W = Int64]` in a rule body's `is_modifiable(Cell[W = Int64])`, or
                // a binding value's `fact Modifiable[T = Cell[V = Int64]]`. `convert_term`
                // is the THIRD path that lowers a written type (WI-709 covered the
                // loader's type-position arm and the typer's value-position arm but not
                // this one), so without the same check a rule body could carry a type
                // argument the sort never declared.
                //
                // Gated on `term_depth > 1` — i.e. NOT a top-level term. At top level the
                // same syntax is an INSTANCE CLAIM, and its argument grammar is a
                // different, richer language that this rule would wrongly reject: an
                // op-bearing instance fact names OPERATIONS (`fact Monad[M = Option,
                // pure = optionPure]`), and a positional on a non-parametric spec is the
                // WI-407 CARRIER slot (`fact NonMonotonicStore[FileStore]`), neither of
                // which is a type parameter. Those shapes have their own checks
                // (`maybe_emit_fact_provides_info`, WI-431); policing them here would
                // reject the stdlib.
                //
                // And keyed on the parse-time provenance `is_type_application` — the
                // BRACKETED surface. A `(…)` call whose functor names a sort is a data
                // CONSTRUCTOR, not a type: `sort Leaf { entity Leaf(name: String) }` makes
                // the bare `Leaf` resolve to the SORT, so `Leaf(name: "tip")` is a
                // sort-headed `Term::Fn` whose named args are FIELDS. Shape cannot tell
                // the two apart — only the surface `[…]` vs `(…)` can, which is why the
                // converter records it (WI-618's `minted` set, same reason).
                //
                // Argument VALUES are never inspected, only their names and count, so a
                // logic variable in an argument (`List[T = ?x]` — the rule-body type
                // pattern reflect rules are written with) passes exactly as a ground one.
                if self.term_depth > 1
                    && self.parsed.terms.is_type_application(parse_id)
                    && self.kb.kind_of(new_functor) == Some(SymbolKind::Sort)
                {
                    let declared = self.kb.type_params_of_sort(new_functor);
                    let named_syms: SmallVec<[Symbol; 2]> =
                        new_named.iter().map(|(s, _)| *s).collect();
                    if let Err(problem) = self.kb.check_sort_type_args(
                        new_functor,
                        &declared,
                        &named_syms,
                        new_pos.len(),
                    ) {
                        let detail = problem.describe(&self.kb, new_functor);
                        self.errors.push(LoadError::InvalidTypeArgument {
                            detail,
                            span: Some(self.parsed.terms.span(parse_id)),
                        });
                    }
                }

                Term::Fn { functor: new_functor, pos_args: new_pos, named_args: new_named }
            }
            Term::Ref(sym) => {
                let new_sym = self.remap_symbol_strict(sym);
                Term::Ref(new_sym)
            }
            Term::Bottom => Term::Bottom,
            Term::Ident(sym) => {
                let new_sym = self.remap_symbol(sym);
                // Promote to Ref if the symbol resolved to a defined name
                if self.kb.symbols.is_resolved(new_sym) {
                    Term::Ref(new_sym)
                } else {
                    Term::Ident(new_sym)
                }
            }
            Term::ParseAux(aux) => {
                // WI-271: parse-only payload (TypeExpr / SortBindings). The
                // let_expr / apply `type_name` / `type_args` children are read
                // and lowered DIRECTLY at the LetExpr / ApplyOrConstructor build
                // sites (which strip the ParseAux first), so those never reach
                // here. The one ParseAux that DOES route through generic
                // `convert_term` is a WRITTEN effect-row binding value in a
                // term-position type-arg slot (`fact Spec[E = {}]`, WI-366 B1):
                // a parse `Term` can't structurally hold a row, so it rides as
                // `ParseAux::TypeExpr(EffectRow(..))` and is lowered HERE via the
                // same `lower_effect_row` the type-aware `provides` path uses, so
                // the fact-head and `provides` rows are byte-identical.
                if let Some(kb_id) = self.lower_effect_row_aux(parse_id) {
                    self.term_map.insert(parse_id.raw(), kb_id);
                    return kb_id;
                }
                unreachable!(
                    "Term::ParseAux({aux:?}) reached convert_term_with_expected — \
                     only a written effect-row binding value routes here; the \
                     LetExpr/ApplyOrConstructor build site must read and lower \
                     its ParseAux directly before recursing",
                );
            }
        };

        let kb_id = self.kb.alloc(kb_term);
        self.term_map.insert(parse_id.raw(), kb_id);

        // Emit Description facts if the variable has inline descriptions
        if let Some(desc_texts) = self.parsed.terms.descriptions.get(&parse_id) {
            let desc_texts = desc_texts.clone();
            for desc_text in &desc_texts {
                self.emit_desc_fact(kb_id, desc_text, self.current_scope);
            }
        }

        kb_id
    }

    // ── Expression conversion ─────────────────────────────────────
    //
    // Converts positional-arg expression terms (from the parse-time IR)
    // into named-arg KB entity terms matching the Expr / Pattern sorts
    // in reflect.anthill. Also populates `kb.term_spans` /
    // `kb.functor_spans` so passes downstream can resolve a span from a
    // stored TermId.

    /// Convert a parse-time expression term into the KB's Expr
    /// representation using a work-stack walker. Each `Visit(parse_id)`
    /// produces a leaf kb_id directly or pushes a `Build` frame +
    /// child Visits; when the frame fires it consumes its children's
    /// kb_ids from the result stack and assembles the parent. Runs in
    /// O(1) host stack regardless of source nesting depth.
    fn convert_expr_term(&mut self, parse_id: TermId) -> (TermId, Rc<NodeOccurrence>) {
        let mut work = std::mem::take(&mut self.expr_work);
        let mut results = std::mem::take(&mut self.expr_results);
        work.clear();
        results.clear();
        // WI-304: occurrence stacks operate directly on `self` (the visit/build
        // arms take `&mut self`). Clear them at entry; they end empty after the
        // root is popped below. `convert_expr_term` is never re-entrant.
        self.expr_occ_results.clear();
        self.expr_match_metas.clear();
        debug_assert_eq!(self.occ_suppress, 0, "convert_expr_term: stale occ_suppress on entry");
        // WI-529: an operation body is value/eval context — `not`/`or` here mean the
        // dispatched Bool VALUE ops, selected in remap_name_str via this flag. Reset to
        // false at the single exit below; assert it is clean on entry so a future
        // reentrant/second caller (this method is documented non-reentrant) trips the
        // assert instead of silently mis-routing the outer frame's boolean operators.
        debug_assert!(!self.in_op_body_value, "convert_expr_term: reentered with in_op_body_value set");
        self.in_op_body_value = true;
        self.expr_body_bottom_recovery = false; // WI-605: per-body flag

        work.push(LoadWorkOp::Visit(parse_id));
        while let Some(op) = work.pop() {
            match op {
                LoadWorkOp::Visit(pid) => self.visit_load(pid, &mut work, &mut results),
                LoadWorkOp::Build(frame) => self.build_load(frame, &mut results),
                LoadWorkOp::PushLocalScope(scope) => {
                    self.local_names_stack.push(scope);
                }
                LoadWorkOp::PopLocalScope => {
                    self.local_names_stack.pop();
                }
                LoadWorkOp::PushOccSuppress => {
                    self.occ_suppress += 1;
                }
                LoadWorkOp::PopOccSuppress => {
                    self.occ_suppress -= 1;
                }
            }
        }
        self.in_op_body_value = false; // WI-529: leave op-body value context
        debug_assert_eq!(results.len(), 1, "iterative loader: expected exactly one result");
        let kb_id = results.pop().expect("iterative loader: empty result stack");
        self.expr_work = work;
        self.expr_results = results;

        // WI-304: pop the single root occurrence built in parallel with the
        // term. `expr_occ_results` was cleared at entry (below) and operated
        // on directly through the walk via `&mut self`.
        debug_assert_eq!(
            self.expr_occ_results.len(),
            1,
            "convert_expr_term: expected exactly one occurrence, got {}",
            self.expr_occ_results.len(),
        );
        let occ = self.expr_occ_results.pop()
            .expect("convert_expr_term: empty occurrence stack");
        debug_assert!(self.expr_match_metas.is_empty(), "convert_expr_term: leftover branch metas");
        (kb_id, occ)
    }

    /// Dispatch a single parse-time expression term: produce a leaf
    /// kb_id directly or push a Build frame + child Visits.
    fn visit_load(
        &mut self,
        parse_id: TermId,
        work: &mut Vec<LoadWorkOp>,
        results: &mut Vec<TermId>,
    ) {
        let parse_term = self.parsed.terms.get(parse_id).clone();
        match parse_term {
            Term::Fn { functor, pos_args, named_args } => {
                let name = self.parsed.symbols.name(functor).to_owned();
                match name.as_str() {
                    "match_expr" => {
                        let branch_count = pos_args.len() - 1;
                        work.push(LoadWorkOp::Build(LoadBuildFrame::MatchExpr {
                            outer_parse_id: parse_id,
                            branch_count,
                        }));
                        for &child in pos_args.iter().rev() {
                            work.push(LoadWorkOp::Visit(child));
                        }
                    }
                    "match_branch" => {
                        // Pattern names are bound for the branch body (and guard).
                        let frame = self.build_pattern_scope_frame(pos_args[0]);
                        // WI-537: a 3rd positional arg is the optional arm guard.
                        let has_guard = pos_args.len() > 2;
                        work.push(LoadWorkOp::Build(LoadBuildFrame::MatchBranch {
                            outer_parse_id: parse_id,
                            has_guard,
                        }));
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PopLocalScope);
                        }
                        // The guard (if present) is visited under the pattern
                        // scope like the body, and pushed before it so it drains
                        // AFTER the body (results order [pattern, body, guard]).
                        if has_guard {
                            work.push(LoadWorkOp::Visit(pos_args[2]));
                        }
                        work.push(LoadWorkOp::Visit(pos_args[1])); // body
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PushLocalScope(frame));
                        }
                        // WI-304: the pattern is a TermId field on the branch,
                        // not a child occurrence — suppress its subtree.
                        work.push(LoadWorkOp::PopOccSuppress);
                        work.push(LoadWorkOp::Visit(pos_args[0])); // pattern
                        work.push(LoadWorkOp::PushOccSuppress);
                    }
                    "if_expr" => {
                        work.push(LoadWorkOp::Build(LoadBuildFrame::IfExpr {
                            outer_parse_id: parse_id,
                        }));
                        work.push(LoadWorkOp::Visit(pos_args[2]));
                        work.push(LoadWorkOp::Visit(pos_args[1]));
                        work.push(LoadWorkOp::Visit(pos_args[0]));
                    }
                    "let_expr" => {
                        // The let-pattern's bound names are in scope for
                        // the body but not for the value, so push the
                        // scope frame between value and body. Pop order
                        // on the stack: build_let → pop_scope → body →
                        // push_scope → value → pattern, so push them in
                        // reverse. Skip the scope ops entirely when the
                        // pattern binds no names (wildcard / literal).
                        let frame = self.build_pattern_scope_frame(pos_args[0]);
                        work.push(LoadWorkOp::Build(LoadBuildFrame::LetExpr {
                            outer_parse_id: parse_id,
                        }));
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PopLocalScope);
                        }
                        work.push(LoadWorkOp::Visit(pos_args[2])); // body
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PushLocalScope(frame));
                        }
                        work.push(LoadWorkOp::Visit(pos_args[1])); // value
                        // WI-304: pattern is a TermId field on the let, not a
                        // child occurrence — suppress its subtree.
                        work.push(LoadWorkOp::PopOccSuppress);
                        work.push(LoadWorkOp::Visit(pos_args[0])); // pattern
                        work.push(LoadWorkOp::PushOccSuppress);
                    }
                    "lambda_expr" => {
                        // Lambda param is in scope for the body.
                        let frame = self.build_pattern_scope_frame(pos_args[0]);
                        work.push(LoadWorkOp::Build(LoadBuildFrame::Lambda {
                            outer_parse_id: parse_id,
                        }));
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PopLocalScope);
                        }
                        work.push(LoadWorkOp::Visit(pos_args[1])); // body
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PushLocalScope(frame));
                        }
                        // WI-304: param is a TermId field on the lambda, not a
                        // child occurrence — suppress its subtree.
                        work.push(LoadWorkOp::PopOccSuppress);
                        work.push(LoadWorkOp::Visit(pos_args[0])); // param
                        work.push(LoadWorkOp::PushOccSuppress);
                    }
                    // WI-605: a bare `(x, acc) -> body` where a lambda was
                    // meant — see `LoadError::ArrowTermInExprPosition` for the
                    // rationale. The gate is pratt PROVENANCE (WI-618): a
                    // minted term IS the infix `->`, exactly; a user-written
                    // `arrow(a, b)` call is never minted and keeps the normal
                    // Apply path with its own accurate diagnostics.
                    // Recover with a Bottom leaf so the walk keeps its
                    // one-result shape; the arrow's children are NOT visited
                    // (visiting them is what produced the old misleading
                    // per-binder cascade). No `create_occurrence`: Bottom is
                    // hash-consed to one shared TermId, and the side-table's
                    // first-write-wins `or_insert` would pin THIS site's span
                    // onto every later Bottom lookup. The flag makes the
                    // op/const loader skip storing the poisoned body so the
                    // typer never sees the Bottom (its loud `BottomExpr`
                    // post-elaboration invariant would otherwise add a second,
                    // internal-jargon error at the same site).
                    n if pratt::is_arrow_functor(n)
                        && self.parsed.terms.is_minted(parse_id) =>
                    {
                        self.errors.push(LoadError::ArrowTermInExprPosition {
                            span: self.parsed.terms.span(parse_id),
                        });
                        self.expr_body_bottom_recovery = true;
                        let kb_id = self.kb.alloc(Term::Bottom);
                        results.push(kb_id);
                        self.push_leaf_occ(kb_id);
                    }
                    "proof_stmt" => {
                        // WI-538: pos_args are [body, conclude?]. The
                        // proof binds no value names, so the body sees
                        // the same scope (no scope frame). Visit body
                        // last so it drains first ([body, conclude?]).
                        let has_conclude = pos_args.len() > 1;
                        work.push(LoadWorkOp::Build(LoadBuildFrame::ProofStmt {
                            outer_parse_id: parse_id,
                            has_conclude,
                        }));
                        if has_conclude {
                            work.push(LoadWorkOp::Visit(pos_args[1])); // conclude
                        }
                        work.push(LoadWorkOp::Visit(pos_args[0])); // body
                    }
                    "pattern_var" => {
                        let kb_id = self.load_pattern_var(parse_id, &pos_args);
                        self.create_occurrence(parse_id, kb_id);
                        results.push(kb_id);
                        self.push_leaf_occ(kb_id);
                    }
                    "pattern_wildcard" => {
                        let kb_id = self.load_pattern_wildcard();
                        self.create_occurrence(parse_id, kb_id);
                        results.push(kb_id);
                        self.push_leaf_occ(kb_id);
                    }
                    "pattern_literal" => {
                        let kb_id = self.load_pattern_literal(&pos_args);
                        self.create_occurrence(parse_id, kb_id);
                        results.push(kb_id);
                        self.push_leaf_occ(kb_id);
                    }
                    "pattern_constructor" => {
                        // The constructor name (pos_args[0]) is a leaf Ident — pre-resolve
                        // it now so the Build frame can drain only the sub-pattern children.
                        let name_term = self.parsed.terms.get(pos_args[0]).clone();
                        let name_ref = if let Term::Ident(sym) = name_term {
                            let kb_sym = self.remap_symbol(sym);
                            self.kb.alloc(Term::Ref(kb_sym))
                        } else {
                            self.convert_term(pos_args[0])
                        };
                        let sub_pattern_count = pos_args.len() - 1;
                        // WI-445: named sub-patterns (`Box(v: some(x))`) ride the
                        // parse term's `named_args`; the old handler read only
                        // `pos_args`, so they were silently dropped at load and
                        // never bound in the typer/eval. Reintern each field name
                        // and Visit its sub-pattern so it survives. Field→position
                        // is resolved later (typer/eval), where the entity's fields
                        // are registered regardless of declaration order.
                        let named_fields: Vec<Symbol> = named_args
                            .iter()
                            .map(|(field_sym, _)| self.reintern(*field_sym))
                            .collect();
                        work.push(LoadWorkOp::Build(LoadBuildFrame::PatternConstructor {
                            outer_parse_id: parse_id,
                            name_ref,
                            sub_pattern_count,
                            named_fields,
                        }));
                        // Push named children FIRST (deeper on the work stack),
                        // then positional (on top), so results drain as
                        // [positional…, named…] — the order the Build frame and
                        // `named_fields` expect.
                        for &(_, child) in named_args.iter().rev() {
                            work.push(LoadWorkOp::Visit(child));
                        }
                        for &child in pos_args[1..].iter().rev() {
                            work.push(LoadWorkOp::Visit(child));
                        }
                    }
                    "dot_apply" => {
                        // Parse shape: pos_args = [receiver, Ident(name),
                        // ...positional]; named_args = named call args. The
                        // name is metadata (pre-resolve, don't Visit); the
                        // receiver + args are children.
                        let name_term = self.parsed.terms.get(pos_args[1]).clone();
                        let name_ref = if let Term::Ident(sym) = name_term {
                            let kb_sym = self.remap_symbol(sym);
                            self.kb.alloc(Term::Ref(kb_sym))
                        } else {
                            self.convert_term(pos_args[1])
                        };
                        let positional = &pos_args[2..];
                        let named_keys: SmallVec<[Symbol; 2]> =
                            named_args.iter().map(|&(sym, _)| sym).collect();
                        work.push(LoadWorkOp::Build(LoadBuildFrame::DotApply {
                            outer_parse_id: parse_id,
                            name_ref,
                            pos_count: positional.len(),
                            named_keys,
                        }));
                        // Push named (reversed), positional (reversed), then
                        // receiver last so it pops/lands first.
                        for &(_, tid) in named_args.iter().rev() {
                            work.push(LoadWorkOp::Visit(tid));
                        }
                        for &tid in positional.iter().rev() {
                            work.push(LoadWorkOp::Visit(tid));
                        }
                        work.push(LoadWorkOp::Visit(pos_args[0]));
                    }
                    "pattern_tuple" => {
                        let element_count = pos_args.len();
                        work.push(LoadWorkOp::Build(LoadBuildFrame::PatternTuple {
                            outer_parse_id: parse_id,
                            element_count,
                        }));
                        for &child in pos_args.iter().rev() {
                            work.push(LoadWorkOp::Visit(child));
                        }
                    }
                    _ => {
                        // WI-271: filter out parse-only auxiliary
                        // children (Term::ParseAux). These hold the
                        // let_expr annotation / apply type-args and
                        // are consumed directly at the
                        // LoadBuildFrame::ApplyOrConstructor build by
                        // `read_parse_call_type_args` and
                        // `read_parse_type_annotation`; the work-stack
                        // walker must not recurse into them.
                        // WI-366 B1: but KEEP a written effect-row binding value
                        // (`operation f() -> Type = Spec[E = {}]`) — the
                        // `Term::ParseAux` arm below lowers it (it is a real
                        // binding value, not a build-site payload).
                        let visible_named: Vec<(Symbol, TermId)> = named_args.iter()
                            .filter(|&&(_, tid)| !self.is_parse_aux(tid) || self.is_effect_row_aux(tid))
                            .copied()
                            .collect();
                        let named_keys: SmallVec<[Symbol; 2]> =
                            visible_named.iter().map(|&(sym, _)| sym).collect();
                        let pos_count = pos_args.len();
                        // WI-443: an identifier-receiver dot call — re-routed
                        // to the DotApply path when the dotted functor's head
                        // segment names a local binding. Gated on no
                        // type-args (the filtered ParseAux children):
                        // `dot_apply` has no type-args channel, and silently
                        // dropping them would be worse than the loud flatten.
                        if named_args.len() == visible_named.len()
                            && self.try_identifier_dot_call(
                                parse_id, &name, &pos_args, &visible_named, work, results,
                            )
                        {
                            return;
                        }
                        // WI-280: a bare-identifier value-receiver FIELD access
                        // (`p.x`) reaches the loader as `field_access(p, Ident(x))`
                        // — the no-call sibling of the WI-443 method-call re-route.
                        // Routed to a zero-arg DotApply when `p`'s root names a
                        // local value; otherwise it keeps the `field_access` path.
                        if name == "field_access"
                            && self.try_identifier_dot_field(parse_id, &pos_args, work)
                        {
                            return;
                        }
                        // WI-714 (proposal 052) — the BARE-QUALIFIED citation
                        // position: a rule cited by a dotted name with NO trailing
                        // `(…)` (`ns.rule` / `Sort.rule`) parses (§6.7) as a
                        // `field_access` chain, not a call. When that chain spells a
                        // name resolving to a RULE, it is the `Relation[T]` value —
                        // collapse it to the SAME reference form the bare UNQUALIFIED
                        // rule name lowers to. AFTER the value-receiver re-route, so a
                        // rule cannot shadow a genuine field access on a local value.
                        if name == "field_access"
                            && self.try_qualified_rule_ref(parse_id, results)
                        {
                            return;
                        }
                        work.push(LoadWorkOp::Build(LoadBuildFrame::ApplyOrConstructor {
                            outer_parse_id: parse_id,
                            functor,
                            pos_count,
                            named_keys,
                        }));
                        for &(_, tid) in visible_named.iter().rev() {
                            work.push(LoadWorkOp::Visit(tid));
                        }
                        for &tid in pos_args.iter().rev() {
                            work.push(LoadWorkOp::Visit(tid));
                        }
                    }
                }
            }
            Term::Const(_) => {
                let kb_id = self.load_literal_expr(parse_id);
                self.create_occurrence(parse_id, kb_id);
                results.push(kb_id);
                self.push_leaf_occ(kb_id);
            }
            Term::Ident(_) => {
                let kb_id = self.load_var_ref(parse_id);
                self.create_occurrence(parse_id, kb_id);
                results.push(kb_id);
                self.push_leaf_occ(kb_id);
            }
            Term::Var(Var::Global(vid)) => {
                let kb_id = self.load_op_body_var(parse_id, vid);
                self.create_occurrence(parse_id, kb_id);
                results.push(kb_id);
                self.push_leaf_occ(kb_id);
            }
            Term::ParseAux(_) => {
                // WI-366 B1: a written effect-row binding value in an op-body
                // type-expression (`operation f() -> Type = Spec[E = {}]`),
                // reached via the kept aux in the ApplyOrConstructor `_` arm
                // above. Lower it the same way the fact-head / rule-body paths do;
                // the occurrence is the MATERIALIZED row, not `push_leaf_occ`
                // (whose `build_expr_leaf` panics on a non-leaf `effects_rows` Fn).
                let kb_id = self.lower_effect_row_aux(parse_id).unwrap_or_else(|| {
                    unreachable!(
                        "Term::ParseAux in op-body expr position must be a written \
                         effect-row binding value (the only aux kept by the \
                         ApplyOrConstructor child filter)",
                    )
                });
                self.create_occurrence(parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let occ = node_occurrence::materialize_from_handle(self.kb, kb_id);
                    self.expr_occ_results.push(occ);
                }
            }
            _ => {
                let kb_id = self.convert_term(parse_id);
                self.create_occurrence(parse_id, kb_id);
                results.push(kb_id);
                self.push_leaf_occ(kb_id);
            }
        }
    }

    /// WI-443: re-route an identifier-receiver dot call. The scope-blind
    /// converter flattens `args.find(...)` into the single dotted functor
    /// name `"args.find"` — at parse time it is indistinguishable from a
    /// sort-companion call like `Stream.find(...)`. Here the scope IS known:
    /// when the head segment names a local binding — a let/lambda/match
    /// binder or an op param — the call becomes the same `Expr::DotApply`
    /// the `?x.m(...)` form produces (typer dot-dispatch on the receiver's
    /// sort, WI-279), with a synthesized `var_ref` receiver (there is no
    /// parse node to Visit). Locals are checked before scope resolution, so
    /// a binder shadows a same-named sort. A head naming a sort/namespace —
    /// or nothing in scope — keeps qualified-name flattening (and its
    /// existing loud unknown-functor diagnostic). Multi-segment tails
    /// (`p.x.m(...)`) are conservatively NOT re-routed (kept flattening,
    /// loud) until chained-receiver synthesis is wanted.
    fn try_identifier_dot_call(
        &mut self,
        parse_id: TermId,
        functor_name: &str,
        pos_args: &[TermId],
        visible_named: &[(Symbol, TermId)],
        work: &mut Vec<LoadWorkOp>,
        results: &mut Vec<TermId>,
    ) -> bool {
        let Some((head, member)) = functor_name.split_once('.') else {
            return false;
        };
        if member.contains('.') {
            return false;
        }
        let Some(head_sym) = self.dot_receiver_binder(head) else {
            return false;
        };
        // Synthesized receiver: the `var_ref(name: Ref(binder))` shape
        // `load_var_ref` builds for a bare identifier reference, plus its
        // leaf occurrence — pushed BEFORE the arg Visits so it lands in the
        // DotApply build frame's receiver slot (`results[drain_start]`).
        let receiver_kb = self.mk_var_ref(head_sym);
        results.push(receiver_kb);
        self.push_leaf_occ(receiver_kb);
        let member_sym = self.remap_name_str(member);
        let name_ref = self.kb.alloc(Term::Ref(member_sym));
        let named_keys: SmallVec<[Symbol; 2]> =
            visible_named.iter().map(|&(sym, _)| sym).collect();
        work.push(LoadWorkOp::Build(LoadBuildFrame::DotApply {
            outer_parse_id: parse_id,
            name_ref,
            pos_count: pos_args.len(),
            named_keys,
        }));
        for &(_, tid) in visible_named.iter().rev() {
            work.push(LoadWorkOp::Visit(tid));
        }
        for &tid in pos_args.iter().rev() {
            work.push(LoadWorkOp::Visit(tid));
        }
        true
    }

    /// The binder a dot-receiver HEAD identifier names, IF it denotes a local
    /// VALUE: a let/lambda/match binder (local-name scope) or an op parameter.
    /// Returns `None` for a sort/namespace head or an unbound name — the
    /// discriminator that keeps those on the qualified-name / `field_access`
    /// path. Locals are consulted first, so a binder shadows a same-named sort.
    /// Shared by the WI-443 method-call re-route ([`Self::try_identifier_dot_call`])
    /// and the WI-280 field-access re-route ([`Self::try_identifier_dot_field`]).
    fn dot_receiver_binder(&self, head: &str) -> Option<Symbol> {
        self.lookup_local_name(head).or_else(|| {
            match self.kb.symbols.resolve_in_scope(head, self.current_scope.raw()) {
                ResolveResult::Found(s) => match self.kb.symbols.get(s) {
                    SymbolDef::Resolved { kind: SymbolKind::Param, .. } => Some(s),
                    _ => None,
                },
                _ => None,
            }
        })
    }

    /// WI-280: re-route a bare-identifier value-receiver FIELD access. The
    /// scope-blind converter lowers `p.x` — a NAME-rooted receiver, since the
    /// `?x.field` VALUE form already became `dot_apply` — to
    /// `field_access(receiver, Ident(x))`. Here the scope IS known: when the
    /// receiver's syntactic ROOT identifier names a local value (a let/lambda/
    /// match binder or an op param), the access becomes the same zero-arg
    /// `Expr::DotApply` the `?x.field` form produces — dispatched by the typer's
    /// field-fallback on the receiver's sort (WI-279). A head naming a
    /// sort/namespace — or an `application` receiver (`Map[K=..].x`) — keeps the
    /// `field_access` path (`false`). The receiver (the parse `field_access`
    /// object) is Visited rather than synthesized, so a chained `p.x.y`
    /// re-routes level by level (each inner `field_access` revisits this arm).
    fn try_identifier_dot_field(
        &mut self,
        parse_id: TermId,
        pos_args: &[TermId],
        work: &mut Vec<LoadWorkOp>,
    ) -> bool {
        // The converter shape is exactly `field_access(object, Ident(field))`.
        if pos_args.len() != 2 {
            return false;
        }
        let Term::Ident(member) = self.parsed.terms.get(pos_args[1]).clone() else {
            return false;
        };
        // Decide by the receiver's root identifier (walk down the `field_access`
        // object chain): re-route iff it names a local value place.
        if self.field_access_root_is_value(pos_args[0]).is_none() {
            return false;
        }
        // The member is field metadata — resolve to a `Ref` (the field is keyed
        // by short name against the receiver's sort at the typer, not in scope),
        // matching the `dot_apply` arm's name handling.
        let kb_member = self.remap_symbol(member);
        let name_ref = self.kb.alloc(Term::Ref(kb_member));
        work.push(LoadWorkOp::Build(LoadBuildFrame::DotApply {
            outer_parse_id: parse_id,
            name_ref,
            pos_count: 0,
            named_keys: SmallVec::new(),
        }));
        // Visit the receiver (object) so it lands in the DotApply receiver slot.
        work.push(LoadWorkOp::Visit(pos_args[0]));
        true
    }

    /// Walk a parse receiver down its `field_access` object chain to the root
    /// atom; if that root is a bare identifier naming a local value, return its
    /// binder symbol. The load-time peer of the converter's `is_value_receiver`
    /// root walk — only NAME-rooted receivers reach the loader as `field_access`
    /// (a value-rooted one already became `dot_apply` in the converter), so the
    /// root identifier is the value-vs-name discriminator.
    fn field_access_root_is_value(&self, receiver: TermId) -> Option<Symbol> {
        let mut cur = receiver;
        loop {
            match self.parsed.terms.get(cur) {
                Term::Ident(sym) => {
                    let name = self.parsed.symbols.name(*sym).to_owned();
                    return self.dot_receiver_binder(&name);
                }
                Term::Fn { functor, pos_args, .. }
                    if self.parsed.symbols.name(*functor) == "field_access"
                        && !pos_args.is_empty() =>
                {
                    cur = pos_args[0];
                }
                _ => return None,
            }
        }
    }

    /// WI-714 (proposal 052) — the BARE-QUALIFIED citation position. A rule cited by
    /// a dotted name with NO trailing `(…)` (`ns.rule`, `Sort.rule` — e.g.
    /// `test.data.person_row`) parses (§6.7) as a `field_access` chain, NOT a call: a
    /// name with no application is dot projection. When that chain's segments spell a
    /// name resolving to a RULE (an unlabeled rule's `Goal` head functor or a `Rule`
    /// label) in scope, it denotes the `Relation[T]` VALUE — exactly as the bare
    /// UNQUALIFIED `person_row` does. Collapse it to the SAME `var_ref(name:
    /// Ref(rule))` form `load_var_ref` lowers the unqualified reference to, so the
    /// existing `check_bare_ref` (C3 schema) + `reduce_var` (C2 value) arms serve all
    /// three citation positions uniformly — no new typer/eval arm, no `CallClass`.
    ///
    /// A value-rooted receiver never reaches here (the converter made it `dot_apply`),
    /// and a LOCAL-value-rooted chain was already re-routed by
    /// [`Self::try_identifier_dot_field`] — so a surviving chain is name-rooted
    /// (sort / namespace), the proposal's §6.7 mode-2 gate implicit in a successful
    /// rule resolution. Resolution is read-only ([`Self::resolve_qualified_rule_readonly`]),
    /// so a chain that is a genuine projection falls through to the ordinary path
    /// untouched.
    fn try_qualified_rule_ref(&mut self, parse_id: TermId, results: &mut Vec<TermId>) -> bool {
        let Some(name) = self.field_access_dotted_name(parse_id) else {
            return false;
        };
        let Some(sym) = self.resolve_qualified_rule_readonly(&name) else {
            return false;
        };
        // Emit the bare-unqualified rule-reference form + its leaf occurrence —
        // mirrors the `Term::Ident` arm of `visit_load` (via `load_var_ref`).
        let kb_id = self.mk_var_ref(sym);
        self.create_occurrence(parse_id, kb_id);
        results.push(kb_id);
        self.push_leaf_occ(kb_id);
        true
    }

    /// The dotted name a pure `field_access(Ident-chain, Ident)` term spells, or
    /// `None` if any node isn't the converter's 2-arg `field_access(object,
    /// Ident(field))` shape bottoming out in a root `Ident` (i.e. a call / value /
    /// instantiation sits in the chain, so it is not a static name path).
    fn field_access_dotted_name(&self, parse_id: TermId) -> Option<String> {
        let mut segments: Vec<String> = Vec::new();
        let mut cur = parse_id;
        loop {
            match self.parsed.terms.get(cur) {
                Term::Ident(sym) => {
                    segments.push(self.parsed.symbols.name(*sym).to_owned());
                    break;
                }
                Term::Fn { functor, pos_args, named_args }
                    if self.parsed.symbols.name(*functor) == "field_access"
                        && pos_args.len() == 2
                        && named_args.is_empty() =>
                {
                    let Term::Ident(field) = self.parsed.terms.get(pos_args[1]) else {
                        return None;
                    };
                    segments.push(self.parsed.symbols.name(*field).to_owned());
                    cur = pos_args[0];
                }
                _ => return None,
            }
        }
        segments.reverse();
        Some(segments.join("."))
    }

    /// Read-only resolution of a dotted `name` to a RULE symbol (`Goal` head functor
    /// or `Rule` label), else `None`. Mirrors the resolution
    /// [`Self::remap_name_str_inner`] performs — direct scope resolution, else a
    /// head-segment-qualified `by_qualified_name` probe (the `ns.rule` / `Map.empty`
    /// shape a single joined name takes) — but WITHOUT its mutation (no
    /// unresolved-name interning, no error push), so a non-rule name leaves loader
    /// state untouched for the ordinary `field_access` projection path.
    fn resolve_qualified_rule_readonly(&self, name: &str) -> Option<Symbol> {
        let scope = self.current_scope.raw();
        let sym = match self.kb.symbols.resolve_in_scope(name, scope) {
            ResolveResult::Found(s) => s,
            _ => {
                let (head, tail) = name.split_once('.')?;
                let ResolveResult::Found(head_sym) =
                    self.kb.symbols.resolve_in_scope(head, scope)
                else {
                    return None;
                };
                let head_qualified = match self.kb.symbols.get(head_sym) {
                    SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                    SymbolDef::Unresolved { name } => name.clone(),
                };
                self.kb
                    .symbols
                    .by_qualified_name
                    .get(&format!("{head_qualified}.{tail}"))
                    .copied()?
            }
        };
        matches!(self.kb.kind_of(sym), Some(SymbolKind::Goal | SymbolKind::Rule)).then_some(sym)
    }

    /// WI-304: push the native leaf `NodeOccurrence` for a just-built leaf
    /// kb_id, unless we're inside a suppressed pattern subtree (where the
    /// pattern is a `TermId` field, not a child occurrence). Mirrors the leaf
    /// arms of `node_occurrence::visit_term`.
    fn push_leaf_occ(&mut self, kb_id: TermId) {
        if self.occ_suppress == 0 {
            let occ = node_occurrence::build_expr_leaf(self.kb, kb_id);
            self.expr_occ_results.push(occ);
        }
    }

    /// Assemble a parent kb_id from its already-converted children
    /// (read in pushed order from the tail of `results`, then truncated).
    fn build_load(&mut self, frame: LoadBuildFrame, results: &mut Vec<TermId>) {
        match frame {
            LoadBuildFrame::MatchExpr { outer_parse_id, branch_count } => {
                let drain_start = results.len() - (branch_count + 1);
                let scrutinee = results[drain_start];
                let branches = build_list(self.kb, &results[drain_start + 1..]);
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.match_expr,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_scrutinee, scrutinee),
                        (s.k_branches, branches),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    let n = self.expr_match_metas.len();
                    let branches = self.expr_match_metas.split_off(n - branch_count);
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::Match { span, branches },
                        &mut self.expr_occ_results,
                    );
                }
            }
            LoadBuildFrame::MatchBranch { outer_parse_id, has_guard } => {
                let n = if has_guard { 3 } else { 2 };
                let drain_start = results.len() - n;
                let pattern = results[drain_start];
                let body = results[drain_start + 1];
                // WI-537: the guard's reshaped KB term (3rd drained result when
                // present) becomes the named `guard: some(g)` slot the occurrence
                // walker reads; `none` for a guardless arm.
                let guard = if has_guard {
                    let g = results[drain_start + 2];
                    build_some(self.kb, g)
                } else {
                    build_none(self.kb)
                };
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.match_branch,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_pattern, pattern),
                        (s.k_guard, guard),
                        (s.k_body, body),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    // WI-304 / WI-537: the body occurrence — and the guard
                    // occurrence when present — are already on `expr_occ_results`
                    // (pattern was suppressed). Record branch metadata for the
                    // enclosing MatchExpr build to drain.
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    self.expr_match_metas.push(node_occurrence::BranchMeta {
                        pattern,
                        has_guard,
                        span,
                    });
                }
            }
            LoadBuildFrame::IfExpr { outer_parse_id } => {
                let drain_start = results.len() - 3;
                let cond = results[drain_start];
                let then_branch = results[drain_start + 1];
                let else_branch = results[drain_start + 2];
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.if_expr,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_cond, cond),
                        (s.k_then, then_branch),
                        (s.k_else, else_branch),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::If { span },
                        &mut self.expr_occ_results,
                    );
                }
            }
            LoadBuildFrame::LetExpr { outer_parse_id } => {
                let drain_start = results.len() - 3;
                let pattern = results[drain_start];
                let value = results[drain_start + 1];
                let body = results[drain_start + 2];
                results.truncate(drain_start);
                let named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::from_slice(&[
                    (self.expr_syms.k_pattern, pattern),
                    (self.expr_syms.k_value, value),
                    (self.expr_syms.k_body, body),
                ]);
                // WI-342 (T8 cleanup): the `let x : T = e1; e2` annotation is
                // carried ONLY by the occurrence's `Let.type_annotation` (a
                // carrier-agnostic `Value`, built below via `type_expr_to_value`).
                // The old term-side `k_type_name` slot on the let_expr `Term::Fn`
                // (WI-271) was write-only — the typer types the let from the
                // occurrence, not the term — so it is dropped, removing a
                // ground-fact caller of the structural type lowering
                // (`type_expr_to_value`). (`read_parse_type_
                // annotation` still feeds the occurrence annotation below.)
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: self.expr_syms.let_expr,
                    pos_args: SmallVec::new(),
                    named_args: named,
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    // WI-342 S4a: the occurrence annotation is a carrier-agnostic
                    // `Value` (a denoted-bearing `: Modify[c]` rides as
                    // `Value::Node`) — lowered from the parse annotation via
                    // `type_expr_to_value`. This is the SOLE carrier of the let
                    // annotation now (the term-side `k_type_name` slot was dropped
                    // in T8 cleanup).
                    let type_annotation = self
                        .read_parse_type_annotation(outer_parse_id)
                        .map(|ty_expr| self.type_expr_to_value(&ty_expr));
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::Let { span, pattern, type_annotation },
                        &mut self.expr_occ_results,
                    );
                }
            }
            LoadBuildFrame::Lambda { outer_parse_id } => {
                let drain_start = results.len() - 2;
                let param = results[drain_start];
                let body = results[drain_start + 1];
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.lambda,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_param, param),
                        (s.k_body, body),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::Lambda { span, param },
                        &mut self.expr_occ_results,
                    );
                }
            }
            LoadBuildFrame::ProofStmt { outer_parse_id, has_conclude } => {
                // WI-538: results drain as [body, conclude?].
                let n = if has_conclude { 2 } else { 1 };
                let drain_start = results.len() - n;
                let body = results[drain_start];
                let conclude = if has_conclude { Some(results[drain_start + 1]) } else { None };
                results.truncate(drain_start);

                let meta = self
                    .read_parse_proof_meta(outer_parse_id)
                    .expect("proof_stmt: missing proof_meta ParseAux");

                // The proof name is a citation handle (conclude form) or
                // a rule reference (short form): a handle is interned
                // as-is (names nothing yet); a rule ref is scope-resolved.
                let target = if has_conclude {
                    let txt = meta
                        .target
                        .segments
                        .last()
                        .map(|s| self.parsed.symbols.name(*s).to_owned())
                        .unwrap_or_else(|| "_proof".to_owned());
                    self.kb.intern(&txt)
                } else {
                    self.remap_name(&meta.target)
                };
                let strategy = meta.strategy_name.map(|s| {
                    let txt = self.parsed.symbols.name(s).to_owned();
                    self.kb.intern(&txt)
                });
                let using: Vec<Symbol> =
                    meta.using.iter().map(|nm| self.remap_name(nm)).collect();

                // KB term: proof_stmt { target, [strategy,] body, [conclude] }.
                // `using` rides only on the occurrence (citation metadata,
                // not a child); a term round-trip drops it.
                let k_target = self.expr_syms.k_target;
                let k_strategy = self.expr_syms.k_strategy;
                let k_body = self.expr_syms.k_body;
                let k_conclude = self.expr_syms.k_conclude;
                let proof_functor = self.expr_syms.proof_stmt;
                let target_term = self.kb.alloc(Term::Ident(target));
                let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                named.push((k_target, target_term));
                if let Some(strat) = strategy {
                    let strat_term = self.kb.alloc(Term::Ident(strat));
                    named.push((k_strategy, strat_term));
                }
                named.push((k_body, body));
                if let Some(c) = conclude {
                    named.push((k_conclude, c));
                }
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: proof_functor,
                    pos_args: SmallVec::new(),
                    named_args: named,
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::Proof { span, target, strategy, using, has_conclude },
                        &mut self.expr_occ_results,
                    );
                }
            }
            LoadBuildFrame::PatternConstructor {
                outer_parse_id,
                name_ref,
                sub_pattern_count,
                named_fields,
            } => {
                // Results drain as [positional…, named…] (see the Visit handler).
                let named_count = named_fields.len();
                let drain_start = results.len() - sub_pattern_count - named_count;
                let pos_end = drain_start + sub_pattern_count;
                let args_list = build_list(self.kb, &results[drain_start..pos_end]);
                // WI-445: each named sub-pattern becomes a reflect
                // `NamedPattern(name: Ref(field), pattern: sub)`, collected under
                // the `named` key — mirroring `named_tuple_pattern`'s
                // `List[NamedPattern]`. Omitted entirely when there are none, so
                // all-positional patterns keep their byte-identical 2-field shape.
                // Shared builder with `pattern_to_term` so the round-trip shape
                // cannot drift.
                let named_subs: Vec<TermId> = named_fields
                    .iter()
                    .zip(results[pos_end..].iter())
                    .map(|(field, &sub_pat)| {
                        node_occurrence::build_named_pattern_term(self.kb, *field, sub_pat)
                    })
                    .collect();
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let mut np: SmallVec<[(Symbol, TermId); 2]> =
                    SmallVec::from_slice(&[(s.k_name, name_ref), (s.k_args, args_list)]);
                if named_count > 0 {
                    let named_list = build_list(self.kb, &named_subs);
                    let k_named = self.expr_syms.k_named;
                    np.push((k_named, named_list));
                }
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: self.expr_syms.constructor_pattern,
                    pos_args: SmallVec::new(),
                    named_args: np,
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                // WI-304: a constructor pattern is only reached inside a
                // suppressed pattern subtree (let/lambda/match pattern), so it
                // never contributes a child occurrence.
                debug_assert!(self.occ_suppress > 0, "pattern_constructor outside suppression");
            }
            LoadBuildFrame::PatternTuple { outer_parse_id, element_count } => {
                let drain_start = results.len() - element_count;
                let elements_list = build_list(self.kb, &results[drain_start..]);
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.tuple_pattern,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[(s.k_elements, elements_list)]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                debug_assert!(self.occ_suppress > 0, "pattern_tuple outside suppression");
            }
            LoadBuildFrame::ApplyOrConstructor {
                outer_parse_id,
                functor: parse_functor,
                pos_count,
                named_keys,
            } => {
                let total = pos_count + named_keys.len();
                let drain_start = results.len() - total;

                let kb_functor = self.remap_symbol(parse_functor);
                let is_entity = matches!(
                    self.kb.symbols.get(kb_functor),
                    SymbolDef::Resolved { kind: SymbolKind::Entity, .. }
                );

                let mut arg_terms: SmallVec<[TermId; 4]> = SmallVec::with_capacity(total);
                for i in 0..pos_count {
                    let value = results[drain_start + i];
                    let none = build_none(self.kb);
                    arg_terms.push(self.mk_apply_arg(none, value));
                }
                for (i, &sym) in named_keys.iter().enumerate() {
                    let value = results[drain_start + pos_count + i];
                    let reinterned = self.reintern(sym);
                    let name_ref = self.kb.alloc(Term::Ref(reinterned));
                    let some_name = build_some(self.kb, name_ref);
                    arg_terms.push(self.mk_apply_arg(some_name, value));
                }
                results.truncate(drain_start);
                let args_list = build_list(self.kb, &arg_terms);
                let name_ref = self.kb.alloc(Term::Ref(kb_functor));

                // WI-342: the occurrence type-args (carrier-agnostic `Value`s) are
                // the source of truth; the term-side `type_args` handle is the
                // ground-only vestige (materialize + print).
                let type_args = self.build_call_type_args(outer_parse_id);
                let type_args_tid = self.type_args_term_handle(&type_args);

                let s = &self.expr_syms;
                let kb_id = if is_entity {
                    self.kb.alloc(Term::Fn {
                        functor: s.constructor,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::from_slice(&[
                            (s.k_name, name_ref),
                            (s.k_args, args_list),
                        ]),
                    })
                } else {
                    let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::from_slice(&[
                        (s.k_fn, name_ref),
                        (s.k_args, args_list),
                    ]);
                    if let Some(tid) = type_args_tid {
                        named.push((s.k_type_args, tid));
                    }
                    self.kb.alloc(Term::Fn {
                        functor: s.apply,
                        pos_args: SmallVec::new(),
                        named_args: named,
                    })
                };
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    // Reintern the parse named keys to the SAME KB symbols the
                    // term's ApplyArg names use (see the named loop above), so
                    // the occurrence's named args line up with the term.
                    let occ_named_keys: Vec<Symbol> =
                        named_keys.iter().map(|s| self.reintern(*s)).collect();
                    let frame = if is_entity {
                        node_occurrence::BuildFrame::Constructor {
                            span, name: kb_functor, pos_count, named_keys: occ_named_keys,
                        }
                    } else {
                        // WI-342: the occurrence carries the carrier-agnostic
                        // `Value` type-args DIRECTLY (built above), not via the
                        // term-handle round-trip — so a value-in-type arg rides as
                        // `Value::Node` rather than being lost to the ground handle.
                        node_occurrence::BuildFrame::Apply {
                            span, functor: kb_functor, pos_count,
                            named_keys: occ_named_keys, type_args,
                        }
                    };
                    node_occurrence::build_frame(self.kb, frame, &mut self.expr_occ_results);
                }
            }
            LoadBuildFrame::DotApply { outer_parse_id, name_ref, pos_count, named_keys } => {
                // Result layout (drain_start..): receiver, positional args,
                // named args. Build the reflect `dot_apply(receiver, name,
                // args: List[ApplyArg])` — the same ApplyArg encoding the
                // apply path uses, so `materialize_from_handle` round-trips it.
                // WI-443: flag the KB — the typer must reassemble ancestor
                // trees for the dot rewrite to persist, even with no [simp].
                self.kb.has_dot_applies = true;
                let total = 1 + pos_count + named_keys.len();
                let drain_start = results.len() - total;
                let receiver = results[drain_start];
                let mut arg_terms: SmallVec<[TermId; 4]> = SmallVec::with_capacity(pos_count + named_keys.len());
                for i in 0..pos_count {
                    let value = results[drain_start + 1 + i];
                    let none = build_none(self.kb);
                    arg_terms.push(self.mk_apply_arg(none, value));
                }
                for (i, &sym) in named_keys.iter().enumerate() {
                    let value = results[drain_start + 1 + pos_count + i];
                    let reinterned = self.reintern(sym);
                    let arg_name = self.kb.alloc(Term::Ref(reinterned));
                    let some_name = build_some(self.kb, arg_name);
                    arg_terms.push(self.mk_apply_arg(some_name, value));
                }
                results.truncate(drain_start);
                let args_list = build_list(self.kb, &arg_terms);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.dot_apply,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_receiver, receiver),
                        (s.k_name, name_ref),
                        (s.k_args, args_list),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    let name = if let Term::Ref(s) = self.kb.get_term(name_ref) {
                        *s
                    } else {
                        panic!("dot_apply name_ref is not a Term::Ref");
                    };
                    let occ_named_keys: Vec<Symbol> =
                        named_keys.iter().map(|s| self.reintern(*s)).collect();
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::DotApply {
                            span, name, pos_count, named_keys: occ_named_keys,
                        },
                        &mut self.expr_occ_results,
                    );
                }
            }
        }
    }

    /// WI-271 / WI-342: lower the parse-side `[A = Int64, B = String]` call
    /// bindings (read from the apply parse Term's `type_args` named arg, a
    /// `Term::ParseAux(SortBindings(...))`) into carrier-agnostic occurrence
    /// type-args `(Option<Symbol>, Value)`: the param label (`A`) as a bare
    /// interned `Symbol` referring to the callee's type-param (NOT a caller-scope
    /// value), and the bound type as a `Value`. A value-in-type bound (the `3` in
    /// `g[3]`) lowers via `type_expr_to_value` to a `Value::Node` denoted — never
    /// re-grounded via `make_denoted`. The occurrence carries these directly
    /// (`BuildFrame::Apply.type_args`); the vestigial term-side handle is built
    /// separately by `type_args_term_handle`. Empty when no explicit bindings.
    fn build_call_type_args(
        &mut self,
        parse_id: TermId,
    ) -> Vec<(Option<Symbol>, crate::eval::value::Value)> {
        let Some(bindings) = self.read_parse_call_type_args(parse_id) else {
            return Vec::new();
        };
        bindings
            .iter()
            .map(|b| {
                let name = b.param.as_ref().map(|name| {
                    let raw = join_segments(&self.parsed.symbols, &name.segments);
                    self.kb.intern(&raw)
                });
                let value = self.type_expr_to_value(&b.bound);
                (name, value)
            })
            .collect()
    }

    /// WI-342: build the vestigial term-side `type_args` handle — a cons-list of
    /// `type_arg(name: Option[Ref], value: Type)` hash-consed terms — from the
    /// occurrence type-args. This handle feeds ONLY occurrence materialization
    /// (`collect_type_args`) and persistence printing; the typer and runtime read
    /// the occurrence / `resolved_type_args` side-table. A `Value::Node`
    /// (value-in-type) entry, which a hash-consed term cannot hold, is OMITTED —
    /// the occurrence is the source of truth and carries it faithfully. Returns
    /// `None` when there is no ground entry (no `type_args` named arg added).
    fn type_args_term_handle(
        &mut self,
        entries: &[(Option<Symbol>, crate::eval::value::Value)],
    ) -> Option<TermId> {
        use crate::eval::value::Value;
        let (type_arg_sym, k_name, k_value) = {
            let s = &self.expr_syms;
            (s.type_arg, s.k_name, s.k_value)
        };
        let term_entries: Vec<TermId> = entries
            .iter()
            .filter_map(|(name, value)| {
                // Omit a value-in-type (Node) entry — see fn doc.
                let value_term = match value {
                    Value::Term { id: t, .. } => *t,
                    _ => return None,
                };
                let name_opt = match name {
                    Some(sym) => {
                        let name_ref = self.kb.alloc(Term::Ref(*sym));
                        build_some(self.kb, name_ref)
                    }
                    None => build_none(self.kb),
                };
                Some(self.kb.alloc(Term::Fn {
                    functor: type_arg_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (k_name, name_opt),
                        (k_value, value_term),
                    ]),
                }))
            })
            .collect();
        if term_entries.is_empty() {
            None
        } else {
            Some(build_list(self.kb, &term_entries))
        }
    }

    /// WI-271: is the term at `id` a parse-only `Term::ParseAux`?
    /// Used by the loader's child-walkers to filter parse-aux children
    /// out of the generic visit/recurse paths — those children are
    /// consumed directly at the LetExpr / ApplyOrConstructor build
    /// sites via `read_parse_*` helpers.
    fn is_parse_aux(&self, id: TermId) -> bool {
        matches!(self.parsed.terms.get(id), Term::ParseAux(_))
    }

    /// WI-366 B1: is the parse term at `id` a WRITTEN effect-row binding value
    /// (`ParseAux::TypeExpr(EffectRow)`, from `fact Spec[E = {}]`)? Unlike the
    /// let/apply build-site ParseAux payloads ([`Self::is_parse_aux`]) — which
    /// are consumed directly at their build sites and filtered out of the generic
    /// child recursion — this one is a real term-position binding value that
    /// `convert_term`'s ParseAux arm lowers in place (via `lower_effect_row`), so
    /// the generic Fn child walk must KEEP it rather than drop it.
    fn is_effect_row_aux(&self, id: TermId) -> bool {
        matches!(self.parsed.terms.get(id),
            Term::ParseAux(aux) if matches!(aux.as_ref(), ParseAux::TypeExpr(TypeExpr::EffectRow(_))))
    }

    /// WI-366 B1: lower a WRITTEN effect-row binding value at `pid` — a
    /// `ParseAux::TypeExpr(EffectRow)` produced for `Spec[E = {}]` in a
    /// term-position type-arg slot — to its KB `effects_rows(EffectExpression)`
    /// ground `TermId`, via the SAME [`Self::lower_effect_row`] the type-aware
    /// `provides` path uses. So a fact head, a rule-body atom, and a `provides`
    /// clause all carry a byte-identical row. Returns `None` when `pid` is not an
    /// effect-row aux (the caller then handles it as a normal child / skips it).
    ///
    /// A denoted-bearing row (`{Modify[c]}`) cannot ride the hash-consed
    /// term/occurrence path — the carrier would have to be a value fact (WI-366
    /// B, gated on effect-expressions-as-types) — so it emits the gated diagnostic
    /// and falls back to the closed-pure row rather than dropping it silently.
    fn lower_effect_row_aux(&mut self, pid: TermId) -> Option<TermId> {
        let effects = match self.parsed.terms.get(pid) {
            Term::ParseAux(aux) => match aux.as_ref() {
                ParseAux::TypeExpr(TypeExpr::EffectRow(effects)) => effects.clone(),
                _ => return None,
            },
            _ => return None,
        };
        let span = SourceSpan::from_span(self.source_id, self.parsed.terms.span(pid));
        let owner = self.current_owner;
        Some(match self.lower_effect_row(&effects, span, owner) {
            node_occurrence::TypeChild::Ground(t) => t,
            node_occurrence::TypeChild::Node(_) => {
                self.diagnose_gated_value_in_type(
                    "type argument",
                    &TypeExpr::EffectRow(effects),
                );
                self.kb.build_canonical_effects_rows(&[])
            }
        })
    }

    /// WI-366 B1: occurrence-form of [`Self::lower_effect_row_aux`] — lower a
    /// written effect-row binding value at `pid` and materialize it as an
    /// `Rc<NodeOccurrence>`, the twin the occurrence-building paths
    /// (`build_body_atom_occurrence`) need where the term path uses the raw
    /// `TermId`. `None` when `pid` is not an effect-row aux.
    fn lower_effect_row_aux_occ(&mut self, pid: TermId) -> Option<Rc<NodeOccurrence>> {
        let rows_tid = self.lower_effect_row_aux(pid)?;
        Some(node_occurrence::materialize_from_handle(self.kb, rows_tid))
    }

    /// WI-271: extract a parse-only `ParseAux` payload from a parent
    /// parse `Term::Fn`'s named arg. `key` is the unresolved parse-side
    /// name (e.g. `"type_name"`, `"type_args"`); `extract` projects the
    /// `ParseAux` enum to the expected inner shape. Returns `None`
    /// when the named arg is absent, points at a non-ParseAux, or its
    /// ParseAux variant doesn't match what `extract` accepts.
    fn read_parse_aux<T>(
        &self,
        parent_id: TermId,
        key: &str,
        extract: impl FnOnce(&crate::parse::ir::ParseAux) -> Option<T>,
    ) -> Option<T> {
        let named_args = match self.parsed.terms.get(parent_id) {
            Term::Fn { named_args, .. } => named_args,
            _ => return None,
        };
        let key_sym = self.parsed.symbols.lookup(key)?;
        let aux_tid = named_args.iter()
            .find(|(s, _)| *s == key_sym)
            .map(|(_, t)| *t)?;
        match self.parsed.terms.get(aux_tid) {
            Term::ParseAux(aux) => extract(aux.as_ref()),
            _ => None,
        }
    }

    /// WI-271: the `let pat : T = …` annotation child of a let_expr.
    fn read_parse_type_annotation(&self, let_parse_id: TermId) -> Option<crate::parse::ir::TypeExpr> {
        self.read_parse_aux(let_parse_id, "type_name", |aux| match aux {
            crate::parse::ir::ParseAux::TypeExpr(ty) => Some(ty.clone()),
            _ => None,
        })
    }

    /// WI-538: read the `ParseAux::ProofStmt` metadata (target /
    /// strategy / using) off a `proof_stmt` parse term.
    fn read_parse_proof_meta(
        &self,
        proof_parse_id: TermId,
    ) -> Option<crate::parse::ir::ProofStmtIr> {
        self.read_parse_aux(proof_parse_id, "proof_meta", |aux| match aux {
            crate::parse::ir::ParseAux::ProofStmt(m) => Some(m.clone()),
            _ => None,
        })
    }

    /// WI-271: the `op[A = Int64, B = String](…)` bindings child of an apply.
    fn read_parse_call_type_args(&self, apply_parse_id: TermId) -> Option<Vec<crate::parse::ir::SortBinding>> {
        self.read_parse_aux(apply_parse_id, "type_args", |aux| match aux {
            crate::parse::ir::ParseAux::SortBindings(bindings) => Some(bindings.clone()),
            _ => None,
        })
    }

    /// Build an `ApplyArg(name: …, value: …)` term using cached syms.
    fn mk_apply_arg(&mut self, name: TermId, value: TermId) -> TermId {
        let s = &self.expr_syms;
        self.kb.alloc(Term::Fn {
            functor: s.apply_arg,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(s.k_name, name), (s.k_value, value)]),
        })
    }

    /// var_ref: Term::Ident(sym) → var_ref(name: Ref(sym))
    /// Uses reintern (plain) — lexical variables are NOT KB symbol references.
    /// WI-246: build the `NodeOccurrence` for one rule-body goal atom — the
    /// rule's resolver/typer goal source — NATIVELY from the parse IR, so a
    /// loaded rule body no longer round-trips through the lossy term→occurrence
    /// `materialize_from_handle` re-inference.
    ///
    /// Generic applications and leaves are built directly: a non-entity,
    /// non-reflect `Term::Fn` becomes `Expr::Apply { functor, pos, named }`
    /// (matching `materialize`'s `UnknownFn` build — a goal atom is just an
    /// application; `occ_head` reads it as a `Functor`), and `Const`/`Var`/
    /// `Ref`/`Ident`/`Bottom` map to their `Expr` leaves. Var identity is shared
    /// with the term body via `self.var_map` (the body-term `convert_term` runs
    /// first, so every body var is already mapped). Source spans are taken from
    /// the parse term — info the term-derived path lost (rule-body terms get no
    /// `term_spans` entry, so `materialize` gave them `empty_span`).
    ///
    /// Falls back to `materialize(convert_term(parse_id))` for:
    /// - entity functors — `convert_term` expands partial fields with fresh vars
    ///   (load.rs); the memoized `convert_term` returns the SAME expanded term so
    ///   the occurrence shares those vars (a native rebuild would mint different
    ///   ones); and
    /// - reflect / control-flow forms (`is_reflect_form_functor`) — whose
    ///   occurrence shape isn't a plain `Apply`.
    /// Both are reachable as nested args too (e.g. `member(?x, cons(..))`); the
    /// memoized `convert_term` keeps every subterm consistent. Narrowing these
    /// fallbacks (native entities / structural reflect patterns, fixing the
    /// `apply(args: ?V)` collapse) is later work.
    ///
    /// WI-710: the entry point is a depth-tracking wrapper around the walk (see
    /// `term_depth`) — a rule BODY is built as occurrences, not terms (WI-246), so this
    /// walk is a second place a written parameterized type is lowered, and it needs the
    /// same top-level-vs-nested reading: a body ATOM is a goal (`:- Modifiable[T = ?t]`,
    /// an instance-fact query), a NESTED sort application is a type
    /// (`is_modifiable(Cell[V = Int64])`).
    fn build_body_atom_occurrence(&mut self, parse_id: TermId) -> Rc<NodeOccurrence> {
        let saved = self.term_depth;
        self.term_depth = saved + 1;
        let occ = self.build_body_atom_occurrence_inner(parse_id);
        self.term_depth = saved;
        occ
    }

    /// The walk itself — see [`Self::build_body_atom_occurrence`], which wraps it to
    /// maintain `term_depth`. Every recursive child re-enters through the wrapper.
    fn build_body_atom_occurrence_inner(&mut self, parse_id: TermId) -> Rc<NodeOccurrence> {
        let parse_term = self.parsed.terms.get(parse_id).clone();
        let span = SourceSpan::from_span(self.source_id, self.parsed.terms.span(parse_id));
        let expr = match parse_term {
            Term::Const(lit) => Expr::Const(lit),
            Term::Var(Var::Global(vid)) => {
                // WI-246: this walk IS the rule body's var-identity source (the
                // term body is gone). Map the parse var to its KB var, minting a
                // fresh one on the first occurrence — mirroring `convert_term`'s
                // `Var::Global` arm — and sharing it across body atoms and the
                // (already-converted) head via the same `var_map`. The De Bruijn
                // closing then collects these from the occurrence body
                // (`collect_occurrence_global_vars_ordered`).
                let kb_vid = if let Some(&mapped) = self.var_map.get(&vid.raw()) {
                    mapped
                } else {
                    let name = self.reintern(vid.name());
                    let new_vid = self.kb.fresh_var(name);
                    self.var_map.insert(vid.raw(), new_vid);
                    new_vid
                };
                // Mirror `convert_term`'s tail (load.rs ~3989): a body variable
                // can carry inline descriptions (`?x {< … >}?`); emit them as
                // Description facts targeting the Global var term, as the dropped
                // term-body `convert_term` walk did. (Entity / reflect-form atoms
                // still emit via the `convert_term` call in the Fn arm below; this
                // covers vars in generic predicate atoms.)
                if let Some(desc_texts) = self.parsed.terms.descriptions.get(&parse_id) {
                    let desc_texts = desc_texts.clone();
                    let target = self.kb.alloc(Term::Var(Var::Global(kb_vid)));
                    for desc_text in &desc_texts {
                        self.emit_desc_fact(target, desc_text, self.current_scope);
                    }
                }
                Expr::Var(Var::Global(kb_vid))
            }
            Term::Var(Var::DeBruijn(n)) => Expr::Var(Var::DeBruijn(n)),
            Term::Var(Var::Rigid(_)) => unreachable!("Var::Rigid in stored parse term"),
            Term::Ref(sym) => Expr::Ref(self.remap_symbol_strict(sym)),
            Term::Ident(sym) => {
                let new_sym = self.remap_symbol(sym);
                // Promote to Ref if the symbol resolved to a defined name —
                // mirrors `convert_term`'s Ident arm + `materialize`'s leaf map.
                if self.kb.symbols.is_resolved(new_sym) {
                    Expr::Ref(new_sym)
                } else {
                    Expr::Ident(new_sym)
                }
            }
            Term::Bottom => Expr::Bottom,
            Term::ParseAux(_) => unreachable!(
                "Term::ParseAux reached build_body_atom_occurrence — a body atom \
                 (or its non-ParseAux child) is never a parse-only payload",
            ),
            Term::Fn { functor, pos_args, named_args } => {
                let new_functor = self.remap_symbol(functor);
                if self.kb.entity_field_names(new_functor).is_some()
                    || node_occurrence::is_reflect_form_functor(self.kb, new_functor)
                {
                    let kb_term = self.convert_term(parse_id); // memoized hit
                    return node_occurrence::materialize_from_handle(self.kb, kb_term);
                }
                // Native generic application. Positional in source order; named
                // ParseAux-filtered (type_args / type_name are read elsewhere)
                // with `reintern`ed keys in source order — matching `convert_term`
                // (no entity-field sort for non-entity functors) and thus the
                // `UnknownFn` materialization.
                // WI-366 B1: a written effect-row binding value (`:- Spec[E = {}]`,
                // or nested/positional `:- Outer[k = Inner[{}]]`) rides as an
                // effect-row ParseAux — lower+materialize it (the same
                // `lower_effect_row` the fact-head / `provides` paths use) rather
                // than recursing into the outer `Term::ParseAux` unreachable
                // (positional) or dropping it via the build-site skip (named).
                let mut pos: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(pos_args.len());
                for &pid in pos_args.iter() {
                    if let Some(child) = self.lower_effect_row_aux_occ(pid) {
                        pos.push(child);
                        continue;
                    }
                    pos.push(self.build_body_atom_occurrence(pid));
                }
                let mut named: Vec<(Symbol, Rc<NodeOccurrence>)> = Vec::new();
                for &(sym, pid) in named_args.iter() {
                    if let Some(child) = self.lower_effect_row_aux_occ(pid) {
                        named.push((self.reintern(sym), child));
                        continue;
                    }
                    if self.is_parse_aux(pid) {
                        continue;
                    }
                    let key = self.reintern(sym);
                    let child = self.build_body_atom_occurrence(pid);
                    named.push((key, child));
                }
                // WI-710: a NESTED, BRACKETED sort application in a rule body is a
                // parameterized TYPE (`is_modifiable(Cell[V = Int64])`) — check its type
                // arguments by the same shared rule the other lowering paths use. Gated
                // exactly as the `convert_term` peer: `term_depth > 1` (a top-level body
                // ATOM with a sort head is a GOAL — `:- Modifiable[T = ?t]`, an
                // instance-fact query), and `is_type_application` (a `(…)` call on a
                // sort-named functor is a data CONSTRUCTOR — `Leaf(name: ?tip)`). Only
                // names and counts are read, so a variable argument passes.
                if self.term_depth > 1
                    && self.parsed.terms.is_type_application(parse_id)
                    && self.kb.kind_of(new_functor) == Some(SymbolKind::Sort)
                {
                    let declared = self.kb.type_params_of_sort(new_functor);
                    let named_syms: SmallVec<[Symbol; 2]> =
                        named.iter().map(|(s, _)| *s).collect();
                    if let Err(problem) =
                        self.kb.check_sort_type_args(new_functor, &declared, &named_syms, pos.len())
                    {
                        let detail = problem.describe(&self.kb, new_functor);
                        self.errors.push(LoadError::InvalidTypeArgument {
                            detail,
                            span: Some(span.span),
                        });
                    }
                }
                Expr::Apply { functor: new_functor, pos_args: pos, named_args: named, type_args: Vec::new() }
            }
        };
        NodeOccurrence::new_expr(expr, span, None)
    }

    fn load_var_ref(&mut self, parse_id: TermId) -> TermId {
        let parse_term = self.parsed.terms.get(parse_id).clone();
        if let Term::Ident(sym) = parse_term {
            let kb_sym = self.remap_symbol(sym);
            self.mk_var_ref(kb_sym)
        } else {
            let name_ref = self.convert_term(parse_id);
            self.mk_var_ref_from_term(name_ref)
        }
    }

    /// WI-487: convert an op-body logical variable (`Expr::Var(Global)`). A
    /// surface `?b` whose name resolves to an op parameter — and is not shadowed
    /// by an in-scope let/lambda/match binder — *refers to* that parameter. The
    /// generic `convert_term` would mint a FRESH logical var, re-interning the
    /// name to a new Symbol, so the body var and the OperationInfo param carry
    /// distinct Symbols and only bridge by short name downstream (eval
    /// `find_local`, the typer's short-name fallback). Bind the body var to the
    /// param's own Symbol instead, so an op_body_node param var Symbol == the
    /// matching `OperationInfo.params[i]` Symbol: the typer's exact `lookup_var`
    /// hits NOW (its short-name fallback is retired), and the shared identity
    /// unblocks the WI-483 method-op fold's symbol-keyed param match. (Eval's
    /// `find_local` still compares short names, so it is unaffected either way.)
    /// Any other `?x` — a genuinely-free var, or one bound by a local binder —
    /// keeps the generic behavior (a fresh var bridged by name).
    ///
    /// The param case is resolved PER OCCURRENCE, NOT via the parse-`vid`-keyed
    /// `var_map`: the parser shares ONE `vid` for every `?b` in an operation
    /// regardless of which binding each occurrence refers to (the param in one
    /// branch, a `b`-named let/match/lambda binder in another — locals are
    /// referenced as `?b` too). Caching by `vid` would let the first-visited
    /// occurrence's Symbol leak onto the others, mistyping a shadowed sibling.
    /// A fresh var per param occurrence is harmless: nothing keys op-body param
    /// vars by var identity (the typer/eval resolve them by name/Symbol, and op
    /// bodies are never De Bruijn-closed). Non-param `?b` (a local-binder ref or
    /// a free var) keeps the generic `var_map`-shared behavior via `convert_term`;
    /// the param path never reads or writes `var_map`, so the two cannot
    /// cross-contaminate even when they share a parse `vid`.
    fn load_op_body_var(&mut self, parse_id: TermId, vid: VarId) -> TermId {
        let name = self.parsed.symbols.name(vid.name()).to_owned();
        // WI-550: a `?x` naming a let/lambda/match binder REFERS to that binder, so
        // bind it to the binder's per-site (gensym) Symbol — the same identity its
        // `var_ref(x)` references and its env type binding carry. The generic
        // `convert_term` path would instead mint a fresh var re-interning the SOURCE
        // name (`intern("x")`), which since alpha-renaming no longer equals the
        // binder's gensym → the typer's by-name var lookup misses and a receiver like
        // `?x.peek()` reports an unresolved sort. Resolved per occurrence (like the
        // param case below): the parser shares one parse `vid` across scopes, so a
        // `vid`-keyed cache would leak a shadowed sibling's identity (WI-487).
        if let Some(local) = self.lookup_local_name(&name) {
            let kb_vid = self.kb.fresh_var(local);
            let kb_id = self.kb.alloc(Term::Var(Var::Global(kb_vid)));
            self.term_map.insert(parse_id.raw(), kb_id);
            return kb_id;
        }
        if let ResolveResult::Found(sym) =
            self.kb.symbols.resolve_in_scope(&name, self.current_scope.raw())
        {
            if matches!(
                self.kb.symbols.get(sym),
                SymbolDef::Resolved { kind: SymbolKind::Param, .. }
            ) {
                let kb_vid = self.kb.fresh_var(sym);
                let kb_id = self.kb.alloc(Term::Var(Var::Global(kb_vid)));
                self.term_map.insert(parse_id.raw(), kb_id);
                return kb_id;
            }
        }
        self.convert_term(parse_id)
    }

    /// Build the canonical `var_ref(name: Ref(sym))` expression term for a
    /// resolved identifier. Shared by `load_var_ref` (parse-node references)
    /// and the WI-443 synthesized dot-call receiver (no parse node).
    fn mk_var_ref(&mut self, kb_sym: Symbol) -> TermId {
        let name_ref = self.kb.alloc(Term::Ref(kb_sym));
        self.mk_var_ref_from_term(name_ref)
    }

    fn mk_var_ref_from_term(&mut self, name_ref: TermId) -> TermId {
        let var_ref_sym = self.kb.resolve_symbol("anthill.reflect.Expr.var_ref");
        let name_key = self.kb.intern("name");
        self.kb.alloc(Term::Fn {
            functor: var_ref_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(name_key, name_ref)]),
        })
    }

    /// Literal constant → int_lit/bigint_lit/float_lit/string_lit/bool_lit
    fn load_literal_expr(&mut self, parse_id: TermId) -> TermId {
        let parse_term = self.parsed.terms.get(parse_id).clone();
        if let Term::Const(ref lit) = parse_term {
            let (entity_name, value_term) = match lit {
                super::term::Literal::Int(n) => (
                    "anthill.reflect.Expr.int_lit",
                    self.kb.alloc(Term::Const(super::term::Literal::Int(*n))),
                ),
                super::term::Literal::BigInt(n) => (
                    "anthill.reflect.Expr.bigint_lit",
                    self.kb.alloc(Term::Const(super::term::Literal::BigInt(n.clone()))),
                ),
                super::term::Literal::Float(f) => (
                    "anthill.reflect.Expr.float_lit",
                    self.kb.alloc(Term::Const(super::term::Literal::Float(*f))),
                ),
                super::term::Literal::String(s) => (
                    "anthill.reflect.Expr.string_lit",
                    self.kb.alloc(Term::Const(super::term::Literal::String(s.clone()))),
                ),
                super::term::Literal::Bool(b) => (
                    "anthill.reflect.Expr.bool_lit",
                    self.kb.alloc(Term::Const(super::term::Literal::Bool(*b))),
                ),
                super::term::Literal::Handle(_, _) => {
                    unreachable!("Handle literals cannot appear in source expressions")
                }
            };
            let entity_sym = self.kb.resolve_symbol(entity_name);
            let value_key = self.kb.intern("value");
            self.kb.alloc(Term::Fn {
                functor: entity_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(value_key, value_term)]),
            })
        } else {
            self.convert_term(parse_id)
        }
    }

    // ── Pattern conversion ───────────────────────────────────────

    /// pattern_var: pos_args[0] = Ident(name)
    ///
    /// WI-517: a type-annotated lambda binder (`lambda (x: T) -> …`, or a
    /// tuple element `lambda (a: A, b: B) -> …`) lowers to this SAME functor
    /// but carries its declared type as a `ParseAux::TypeExpr` under the
    /// `type` named arg (set by `convert.rs`'s `typed_binder` arm). When
    /// present, lower it via the SAME `type_expr_to_value` the let-annotation
    /// path uses and materialize a TermId for the var_pattern's `type_ann`
    /// slot, which the typer reads to constrain inference. A bare binder has
    /// no `type` arg, so `type_ann` stays `none()`.
    fn load_pattern_var(&mut self, parse_id: TermId, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let name_term = self.parsed.terms.get(pos_args[0]).clone();
        let name_ref = if let Term::Ident(sym) = name_term {
            // WI-550: the binder's identity is the per-site fresh Symbol minted
            // (keyed by this `pattern_var` node) when its scope frame was built —
            // NOT `reintern(sym)`, which would dedup `let x; let x` to one symbol
            // and collide their Γ facts. `binder_sym` get-or-mints, so an
            // un-framed pattern (none reach here) still gets a unique identity.
            let name = self.parsed.symbols.name(sym).to_owned();
            let kb_sym = self.binder_sym(&name, parse_id);
            self.kb.alloc(Term::Ref(kb_sym))
        } else {
            self.convert_term(pos_args[0])
        };
        let type_ann = match self.read_parse_aux(parse_id, "type", |aux| match aux {
            crate::parse::ir::ParseAux::TypeExpr(ty) => Some(ty.clone()),
            _ => None,
        }) {
            Some(ty_expr) => {
                let value = self.type_expr_to_value(&ty_expr);
                // `value_to_term` is the total Value→Term boundary (WI-390):
                // `type_expr_to_value` yields only `Term`/`Node`, both of which
                // lower without error (ground types ride through unchanged, a
                // `denoted`-bearing type lowers losslessly), so the `Err` branch
                // can't fire. Guard it loudly (debug-assert) rather than
                // silently dropping the annotation — mirrors the `value_to_term`
                // call in `node_occurrence::type_node_to_term`.
                let type_tid = node_occurrence::value_to_term(&mut self.kb, &value)
                    .unwrap_or_else(|e| {
                        debug_assert!(false, "WI-517: binder type annotation not term-representable: {e:?}");
                        self.kb.alloc(Term::Bottom)
                    });
                build_some(self.kb, type_tid)
            }
            None => build_none(self.kb),
        };
        let var_pattern_sym = self.kb.resolve_symbol("anthill.reflect.Pattern.var_pattern");
        let name_key = self.kb.intern("name");
        let type_ann_key = self.kb.intern("type_ann");
        self.kb.alloc(Term::Fn {
            functor: var_pattern_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(name_key, name_ref), (type_ann_key, type_ann)]),
        })
    }

    /// pattern_wildcard: no args
    fn load_pattern_wildcard(&mut self) -> TermId {
        let wildcard_sym = self.kb.resolve_symbol("anthill.reflect.Pattern.wildcard");
        self.kb.alloc(Term::Fn {
            functor: wildcard_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// pattern_literal: pos_args[0] = literal term
    fn load_pattern_literal(&mut self, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let value = self.convert_term(pos_args[0]);
        let lit_pattern_sym = self.kb.resolve_symbol("anthill.reflect.Pattern.literal_pattern");
        let value_key = self.kb.intern("value");
        self.kb.alloc(Term::Fn {
            functor: lit_pattern_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(value_key, value)]),
        })
    }

    /// Find the `Var` target of `SortAlias(<sym>, Var)`. Matches by
    /// exact `Symbol` identity first (one pass), then by short name as
    /// a fallback (second pass). The two-pass order matters: short-name
    /// resolution is ambiguous when many sorts share a type-param name
    /// (`sort T = ?` in List, Option, Stream …), and an exact match
    /// elsewhere in the table must take precedence over an earlier
    /// short-name hit.
    fn find_sort_alias_var(&self, sym: Symbol) -> Option<TermId> {
        let alias_sym = self.kb.try_resolve_symbol("SortAlias")?;
        let sort_name = self.kb.resolve_sym(sym);
        let scan = |matches: &dyn Fn(Symbol, &str) -> bool| -> Option<TermId> {
            for rid in self.kb.rules_by_functor(alias_sym) {
                if !self.kb.is_fact(rid) { continue; }
                // A value-fact SortAlias (denoted-bearing target, e.g.
                // `sort T = Vector[Int64, 3]`) never has a logic `Var` target, so it
                // can't be the type-param indirection we're after — skip it (this
                // also avoids the term-only `rule_head` panic on a `Value::Node`
                // head). Type-param aliases (`sort T = ?`) stay ground `Term`s.
                let Some(head) = self.kb.fact_head_term(rid) else { continue };
                let Term::Fn { pos_args, .. } = self.kb.get_term(head) else { continue };
                if pos_args.len() < 2 { continue; }
                let Term::Fn { functor, .. } = self.kb.get_term(pos_args[0]) else { continue };
                if !matches(*functor, self.kb.resolve_sym(*functor)) { continue; }
                if matches!(self.kb.get_term(pos_args[1]), Term::Var(_)) {
                    return Some(pos_args[1]);
                }
            }
            None
        };
        scan(&|f, _| f == sym).or_else(|| scan(&|_, n| n == sort_name))
    }

    fn name_to_sort_term(&mut self, name: &Name) -> TermId {
        let functor = self.remap_name(name);
        self.kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// WI-341: bind a callback parameter's arrow param names to their registered
    /// `CallbackParam` place symbols, so a self-referential arrow effect
    /// (`Modify[a]`) resolves to the place `<op>.f.a` — the binder's canonical
    /// name from the op frame (doc §2). The places are read straight off the
    /// callback symbol's `arg_places` (set by `register_callback_places`), which
    /// is authoritative and already excludes the arrow `result` (so it is not
    /// bound and cannot shadow the op's reserved `result`) and handles the
    /// unnamed/`result`-named conventions — unlike reconstructing qualified
    /// strings. Each binder is keyed by the place's own short name (`…f.a` → `a`).
    /// A non-callback param has empty `arg_places`, leaving the scope empty.
    /// Nested-arrow params (`f.g.x`) are out of v1 scope (only the top-level
    /// callback's `arg_places` are bound; the arrow case suspends the scope while
    /// converting nested arrows, so their effects do not see this binder).
    fn set_arrow_binder_scope(&mut self, callback_sym: Symbol) {
        self.arrow_binder_scope.clear();
        let places: Vec<Symbol> = self.kb.symbols.arg_places(callback_sym).to_vec();
        for place in places {
            if let Some(short) = self.kb.qualified_name_of(place).rsplit('.').next() {
                let short = short.to_owned();
                self.arrow_binder_scope.insert(short, place);
            }
        }
    }

    /// WI-342: the hash-consed logic `Var` (`TermId`) for a `Simple` type name
    /// that is a type parameter in the current scope. A type param is a ground
    /// `Var` (no `denoted`), shared by all references to the same param within a
    /// scope via the `type_param_vars` cache. Used by the `Simple` arm of
    /// [`Self::type_expr_to_child`] (the sole, carrier-agnostic type lowering) to
    /// build the type-param `Var` directly.
    fn type_param_var(&mut self, sort_sym: Symbol, short_name: &str) -> TermId {
        let key = (self.current_scope.raw(), short_name.to_owned());
        if let Some(&cached) = self.type_param_vars.get(&key) {
            return cached;
        }
        // Try SortAlias first (if abstract sort already loaded).
        let var_tid = if let Some(alias_var) = self.find_sort_alias_var(sort_sym) {
            alias_var
        } else {
            let var_sym = self.kb.intern(short_name);
            let vid = self.kb.fresh_var(var_sym);
            self.kb.alloc(Term::Var(Var::Global(vid)))
        };
        self.type_param_vars.insert(key, var_tid);
        var_tid
    }

    /// WI-342: lift a ground value `TermId` (a value-in-type literal — the `3`
    /// in `Vector[Int64, 3]` / `g[3]`) into a value `NodeOccurrence` for a
    /// `denoted` occurrence's `value` slot. The converter only emits
    /// `TypeExpr::Denoted` for literals (convert.rs), so a `Term::Const` leaf is
    /// the sole expected shape; anything else is a loader bug (error early).
    fn value_term_to_occ(
        &self,
        t: TermId,
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        let expr = match self.kb.get_term(t) {
            Term::Const(lit) => Expr::Const(lit.clone()),
            other => panic!(
                "WI-342: a value-in-type `denoted` value must be a literal \
                 (TypeExpr::Denoted is only emitted for literals), got {other:?}"
            ),
        };
        NodeOccurrence::new_expr(expr, span, owner)
    }

    /// WI-342 — lower a `TypeExpr` to a carrier-agnostic [`Value`], honoring the
    /// carrier rule: a type whose structure transitively contains a `denoted`
    /// (`Modify[c]`, a value-in-type field) is minted as a `Value::Node`
    /// occurrence; a fully-ground type rides as `Value::Term` (the hash-consed
    /// form). WI-366: the SOLE type lowering (the former ground-only
    /// `type_expr_to_term` is retired) — used for operation effect labels, entity
    /// field types, and the sort-relation specs (`SortAlias` / `SortView`
    /// `requires` / fact `provides`, via `sort_inst_to_value`). A thin wrapper
    /// over [`Self::type_expr_to_child`].
    fn type_expr_to_value(&mut self, ty: &TypeExpr) -> crate::eval::value::Value {
        let span = self.type_expr_span(ty);
        let owner = self.current_owner;
        match self.type_expr_to_child(ty, span, owner) {
            node_occurrence::TypeChild::Ground(t) => crate::eval::value::Value::term(t),
            node_occurrence::TypeChild::Node(n) => crate::eval::value::Value::Node(n),
        }
    }

    /// Span for a lowered type's occurrence — its leading `Name` span when
    /// available, else a synthetic span on the current source. Occurrence spans
    /// here feed diagnostics only.
    fn type_expr_span(&self, ty: &TypeExpr) -> SourceSpan {
        match ty {
            TypeExpr::Simple(n) | TypeExpr::Parameterized { name: n, .. } => {
                SourceSpan::from_span(self.source_id, n.span)
            }
            _ => SourceSpan::new(self.source_id, 0, 0),
        }
    }

    /// The structural type lowering (WI-366: absorbed the ground arms of the
    /// retired `type_expr_to_term`), returning a [`node_occurrence::TypeChild`]:
    /// `Ground(TermId)` when the sub-tree is fully ground (the hash-consed form),
    /// or `Node(Rc<NodeOccurrence>)` when it carries a `denoted`. The carrier of a
    /// `parameterized` follows its bindings — any `Node` binding poisons the
    /// whole type to `Node`. Only the value-in-type shapes are Node-aware
    /// (`Simple`-as-value, `Parameterized`); every other shape (arrow, tuple, …)
    /// stays ground (no denoted ⇒ no carrier obligation).
    /// WI-376: classify a multi-segment type name as an expression-carried type
    /// projection `s.T` / `s.Sort` when its HEAD resolves (in the current scope) to
    /// a VALUE binder — a param / local / field / op-result / callback place. The
    /// receiver is `segments[..n-1]`, the projected member is the last segment.
    ///
    /// Returns `None` when the head is NOT a value (a qualified sort ref / namespace
    /// path, or an unresolved name) so the caller falls back to the sort-ref path —
    /// this is the discriminator the WI-302 `denoted` classifier uses for the
    /// single-segment case, lifted to the multi-segment projection.
    ///
    /// A single-segment (ref) receiver — `s.T` — rides as a fully-ground term
    /// `Fn{ExprCarried, value: Ref(s), member: Ref(M)}` (the receiver occurrence is
    /// the ground reference). A COMPOUND receiver (`a.b.T`, a field path) needs the
    /// `TypeNode::ExprCarried` Node carrier, which is the documented follow-on; it is
    /// surfaced as a loud load error here rather than silently mis-lowered.
    fn try_expr_carried_projection(
        &mut self,
        name: &Name,
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> Option<node_occurrence::TypeChild> {
        // `span` / `owner` are unused by the single-ref ground path but carried into
        // the compound-receiver occurrence (WI-397) below.
        let segs = &name.segments;
        // The MEMBER (last segment) of a TYPE projection is Capitalized — a type member
        // (`T`, `Sort`, `E`), per the value-vs-type case rule (type-parameter-scoping.md
        // §1: types/sort-params are Capitalized, value fields lowercase). A lowercase
        // last segment is a VALUE field / place access (`Modify[result.a]`, `x.head`),
        // NOT a type projection — leave it to the denoted / sort-ref path (`None`). This
        // is the discriminator that keeps the per-result-component effect syntax
        // (`Modify[result.a]`, WI-261) lowering to a denoted place, not an ExprCarried.
        let member_name = self.parsed.symbols.name(*segs.last().unwrap()).to_owned();
        if !member_name.chars().next().is_some_and(|c| c.is_uppercase()) {
            return None;
        }
        let head_name = self.parsed.symbols.name(segs[0]).to_owned();
        // WI-400 increment C: a let / lambda / match LOCAL is a value head too — consult
        // the local-name scope stack first (mirrors `remap_symbol`), so a projection off a
        // let-bound receiver (`let y = …; … : y.K`) resolves its head. A local binding is
        // definitionally a value, so it skips the value-head sort/namespace gate that keeps
        // a namespace / sort head (`Foo.T`) on the normal `remap_name` path.
        let head_sym = if let Some(local) = self.lookup_local_name(&head_name) {
            local
        } else {
            let resolved = match self.kb.symbols.resolve_in_scope(&head_name, self.current_scope.raw()) {
                ResolveResult::Found(s) => s,
                _ => return None,
            };
            // A projection's receiver is a VALUE; a namespace / sort head is a qualified
            // sort ref, handled by the normal `remap_name` path (return `None`).
            if !self.symbol_is_value_place(resolved) {
                // WI-428: a TYPE head — a rigid type-parameter (`P.Key`) or a sort
                // (`MemStore.Key`) — classifies as a `RigidTypeProjection`, the
                // type-keyed sibling of `ExprCarried` (design §5.3). Two-segment only;
                // anything else stays on the `remap_name` path.
                if segs.len() == 2 {
                    if let Some(child) =
                        self.try_rigid_type_projection(resolved, &head_name, &member_name, span)
                    {
                        return Some(child);
                    }
                }
                return None;
            }
            resolved
        };
        let member_sym = self.kb.intern(&member_name);
        if segs.len() == 2 {
            // Single value-reference receiver: a ground occurrence `Ref(head)`. The
            // resulting `ExprCarried` term is fully ground (receiver + member both
            // ground), so it rides as a hash-consed `TypeChild::Ground`.
            let receiver_term = self.kb.alloc(crate::kb::term::Term::Ref(head_sym));
            Some(node_occurrence::TypeChild::Ground(
                self.kb.make_expr_carried(receiver_term, member_sym),
            ))
        } else {
            // A COMPOUND receiver (`a.b.T`) projects off a field-access occurrence
            // (WI-397). Build the receiver value path `segs[0..n-1]` as a `DotApply`
            // chain over the value head (`s` then `.provider` …), then wrap it plus the
            // member in the `TypeNode::ExprCarried` Node carrier — the receiver is an
            // `Expr` occurrence (now structural in `occ_head`), so (unlike the single-ref
            // form) the projection cannot hash-cons. The eliminator resolves the path's
            // static type at the call site.
            let mut receiver = NodeOccurrence::new_expr(Expr::Ref(head_sym), span, owner);
            for &field_seg in &segs[1..segs.len() - 1] {
                let field_name = self.parsed.symbols.name(field_seg).to_owned();
                let field_sym = self.kb.intern(&field_name);
                receiver = NodeOccurrence::new_expr(
                    Expr::DotApply {
                        receiver,
                        name: field_sym,
                        pos_args: Vec::new(),
                        named_args: Vec::new(),
                    },
                    span,
                    owner,
                );
            }
            Some(node_occurrence::TypeChild::Node(
                self.kb.make_expr_carried_occ(receiver, member_sym, span, owner),
            ))
        }
    }

    /// Is `sym` a VALUE PLACE — a param / field / local / op-result / callback
    /// binder? This is the value-vs-sort discriminator the three value-in-type
    /// classifiers share (the single-segment `denoted` arm, the compound `denoted`
    /// path [`Self::try_denoted_value_path`], and the type-projection head in
    /// [`Self::try_expr_carried_projection`]) — ONE source of truth so the set cannot
    /// drift between copies. NB the SINGLE-segment denoted arm additionally treats a
    /// zero-arg `Operation` as a value (WI-313 ambient-KB accessor — `Modify[op]`); a
    /// field path projected off an operation NAME is not a value place, so the
    /// compound heads here deliberately omit `Operation`.
    fn symbol_is_value_place(&self, sym: Symbol) -> bool {
        matches!(
            self.kb.symbols.get(sym),
            SymbolDef::Resolved { kind, .. } if kind.is_value_place()
        )
    }

    /// WI-302 (proposal 027.1 per-projection): classify a MULTI-segment dotted name
    /// in a type-argument slot whose HEAD resolves (in scope) to a VALUE and whose
    /// last segment is a VALUE FIELD (lowercase) — `Modify[result.a]`,
    /// `Modify[c.contents]` — as a value-in-type DENOTED PLACE: the value `c.contents`
    /// (the field-access chain) indexing the effect/type. This is the COMPOUND peer of
    /// the single-segment `denoted` value-in-type (the `is_value` arm below) and the
    /// lowercase-last twin of [`Self::try_expr_carried_projection`]'s uppercase-last
    /// TYPE projection. Without it, `type_expr_to_child_inner`'s `remap_name` fallback
    /// joins the segments into an unresolvable `"c.contents"` and emits a stray
    /// `unresolved name` diagnostic (the silent-skip the loud-error principle forbids).
    ///
    /// Returns `None` when the head is NOT a value (a qualified sort ref / namespace
    /// path, or an unresolved name) so the caller falls back to the normal path — the
    /// same value-head discriminator the projection sibling uses. The whole segment
    /// path (including the last) is a value field access, so unlike the projection it
    /// has no separate "member"; the value occurrence carries every `.field` segment.
    fn try_denoted_value_path(
        &mut self,
        name: &Name,
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> Option<node_occurrence::TypeChild> {
        let segs = &name.segments;
        let head_name = self.parsed.symbols.name(segs[0]).to_owned();
        // A let / lambda / match LOCAL is a value head (mirrors the projection sibling);
        // otherwise the head must resolve to a value binder. A namespace / sort head is
        // a qualified ref, left to the normal path (`None`).
        let head_sym = if let Some(local) = self.lookup_local_name(&head_name) {
            local
        } else {
            let resolved = match self.kb.symbols.resolve_in_scope(&head_name, self.current_scope.raw()) {
                ResolveResult::Found(s) => s,
                _ => return None,
            };
            if !self.symbol_is_value_place(resolved) {
                return None;
            }
            resolved
        };
        // WI-489: validate the field path against the head's statically-known type
        // (a param / `result` of the signature being loaded). The v1 denoted place
        // interns field names raw and defers resolution to the elimination/eval site,
        // so a projection onto a NON-EXISTENT field of a concrete-typed head
        // (`Modify[result.nonexistent]`, `Modify[c.bogus]`) would otherwise be
        // silently accepted at load. The head is already validated (an unresolved head
        // returned `None` above ⇒ loud unresolved-name); this validates the tail.
        // Honors the repo "loud error over silent skip" principle.
        self.validate_denoted_field_path(head_sym, segs, &head_name, span);
        // Build the value field-access path over ALL segments (`Ref(head)` then a
        // `.field` `DotApply` per remaining segment), then wrap it in a `denoted`
        // occurrence — the value indexing the type. The field names are interned raw;
        // the access resolves at the elimination/eval site (the v1 representation, like
        // the single-ref `denoted` carrier).
        let mut value = NodeOccurrence::new_expr(Expr::Ref(head_sym), span, owner);
        for &field_seg in &segs[1..] {
            let field_name = self.parsed.symbols.name(field_seg).to_owned();
            let field_sym = self.kb.intern(&field_name);
            value = NodeOccurrence::new_expr(
                Expr::DotApply {
                    receiver: value,
                    name: field_sym,
                    pos_args: Vec::new(),
                    named_args: Vec::new(),
                },
                span,
                owner,
            );
        }
        Some(node_occurrence::TypeChild::Node(
            self.kb.make_denoted_occ(value, span, owner),
        ))
    }

    /// WI-489: validate a value-in-type field projection's tail against the head's
    /// statically-known type. `head_sym` is the resolved projection head (segs[0]);
    /// `segs[1..]` are the field segments. When the head is a param / `result` of the
    /// signature being loaded (in [`Self::signature_place_types`]), walk each segment
    /// against the running type: a NON-EXISTENT field on a CONCRETE type (entity /
    /// named-tuple) is a loud load error; an ABSTRACT / unknown running type (a bare
    /// type-param, a spec with no fields, a builtin, a non-data shape) DEFERS — the
    /// field is genuinely unknowable until the carrier is concrete (the legitimately-
    /// deferred `s.T` / `s.E` projections, WI-376/WI-475, must not regress). A head not
    /// in the map (a local, a cross-context place) also defers — never a false reject.
    fn validate_denoted_field_path(
        &mut self,
        head_sym: Symbol,
        segs: &[Symbol],
        head_name: &str,
        span: SourceSpan,
    ) {
        let Some(head_ty) = self.signature_place_types.get(&head_sym).cloned() else {
            return;
        };
        let mut running = head_ty;
        let mut path = head_name.to_owned();
        for &field_seg in &segs[1..] {
            let field_name = self.parsed.symbols.name(field_seg).to_owned();
            match self.field_step_in_value(&running, &field_name) {
                FieldStep::Found(next) => {
                    running = next;
                    path = format!("{path}.{field_name}");
                }
                FieldStep::NoField { type_display } => {
                    self.errors.push(LoadError::InvalidFieldProjection {
                        path: format!("{path}.{field_name}"),
                        field: field_name,
                        type_display,
                        span: span.span,
                    });
                    return;
                }
                // Abstract / unknown running type: resolution is genuinely deferred to
                // the elimination site — stop walking (a later segment is unknowable).
                FieldStep::Defer => return,
            }
        }
    }

    /// WI-489: resolve one field segment against a type [`Value`], for
    /// [`Self::validate_denoted_field_path`]. Returns the field's declared type
    /// ([`FieldStep::Found`]) so a multi-level path (`c.inner.slot`) keeps walking; a
    /// concrete type that lacks the field ([`FieldStep::NoField`]); or
    /// [`FieldStep::Defer`] when the type is not a concretely-known data shape (a bare
    /// type-param, a sort with no registered fields — a spec / builtin — an arrow, an
    /// effect row, a denoted/projection neutral), where the field is only knowable once
    /// the carrier is concrete.
    fn field_step_in_value(&mut self, ty: &Value, field_name: &str) -> FieldStep {
        match extract_type(self.kb, ty) {
            TypeExtractor::NamedTuple(fields) => {
                // Named field first (a field literally named `_1` wins over positional).
                if let Some((_, v)) =
                    fields.iter().find(|(s, _)| self.kb.resolve_sym(*s) == field_name)
                {
                    return FieldStep::Found(v.clone());
                }
                // Positional `_n` (1-based) into the tuple's fields — `result._1`. The
                // field-ORDER semantics are the eliminator's; for existence an in-range
                // index suffices, so this never falsely rejects a valid positional ref.
                if let Some(idx) = field_name
                    .strip_prefix('_')
                    .and_then(|n| n.parse::<usize>().ok())
                    .filter(|&n| n >= 1)
                {
                    if let Some((_, v)) = fields.get(idx - 1) {
                        return FieldStep::Found(v.clone());
                    }
                }
                FieldStep::NoField { type_display: "named tuple".to_owned() }
            }
            TypeExtractor::SortRef(sort) | TypeExtractor::Parameterized { base: sort, .. } => {
                let field_sym = self.kb.intern(field_name);
                let mut found: Option<Value> = None;
                let mut divergent = false;
                let mut has_fields = false;
                // WI-490: `field_constructors_of_sort` adds a free-standing entity's own
                // symbol (whose `entity_field_types` carries fields a parent-keyed
                // `constructors_of_sort` would miss), so this covers both an entity
                // variant of a sort and a free-standing `entity Pose(x, y)`.
                //
                // Collect from EVERY constructor (no break) so the result is INDEPENDENT
                // of the `field_constructors_of_sort` (HashMap) iteration order, mirroring
                // the eliminator's `resolve_field_type`. If variants declare the field at
                // structurally DIFFERENT types, the continued-walk type is ambiguous —
                // DEFER (the field still EXISTS, so never a false reject; a deeper segment
                // is left to the eliminator, which reports the divergence) rather than
                // pick an order-dependent type.
                for ctor in self.kb.field_constructors_of_sort(sort) {
                    if let Some(fields) = self.kb.entity_field_types(ctor) {
                        has_fields = true;
                        if let Some((_, v)) = fields.iter().find(|(f, _)| *f == field_sym) {
                            match &found {
                                None => found = Some(v.clone()),
                                // WI-486: carrier-agnostic compare — two field
                                // types of the same structure may ride as
                                // different `Value` carriers across constructors.
                                Some(prev)
                                    if crate::kb::term_view::views_structurally_equal(
                                        &self.kb, prev, v,
                                    ) => {}
                                Some(_) => divergent = true,
                            }
                        }
                    }
                }
                match found {
                    // Field exists with one agreed type ⇒ continue the walk.
                    Some(v) if !divergent => FieldStep::Found(v),
                    // Field exists but variants disagree on its type ⇒ exists, so not a
                    // reject; defer the (ambiguous) continued walk to the eliminator.
                    Some(_) => FieldStep::Defer,
                    // A data sort that declares fields but not THIS one ⇒ loud reject.
                    None if has_fields => {
                        FieldStep::NoField { type_display: self.kb.qualified_name_of(sort).to_owned() }
                    }
                    // No registered fields at all — a spec / builtin / abstract sort:
                    // its fields are not statically known here, so defer.
                    None => FieldStep::Defer,
                }
            }
            // A bare type-param, an arrow, an effect row, a denoted/projection neutral,
            // or a malformed type: not a concretely-known data shape ⇒ defer.
            _ => FieldStep::Defer,
        }
    }

    /// WI-428: the LOGICAL sort qualified name behind a resolved symbol that may be
    /// the INNER self-named registration of a sort (`ns.W.P.P`, like
    /// `anthill.prelude.List.List`): strip the duplicated level iff the outer name
    /// also ends in `short` AND maps to a Sort-kind symbol (so a sort merely sharing
    /// its namespace's last segment — `namespace app.Config` containing `sort Config`,
    /// qn `app.Config.Config` — is NOT stripped: `app.Config` is a Namespace).
    fn logical_sort_qn<'q>(&self, qn: &'q str, short: &str) -> &'q str {
        if let Some((outer, last)) = qn.rsplit_once('.') {
            if last == short && outer.rsplit('.').next() == Some(short) {
                if let Some(outer_sym) = self.kb.symbols.by_qualified_name.get(outer) {
                    if matches!(
                        self.kb.symbols.get(*outer_sym),
                        SymbolDef::Resolved { kind: SymbolKind::Sort, .. }
                    ) {
                        return outer;
                    }
                }
            }
        }
        qn
    }

    /// WI-428: classify a two-segment TYPE-headed name (`P.Key` / `MemStore.Key` /
    /// `Storage.Key`) as a `RigidTypeProjection` — the type-keyed sibling of the
    /// value-headed `ExprCarried` (design path-dependent-types.md §5.3). Formation
    /// VALIDATION (the member is declared by a `requires` bound / the projection is
    /// manifest) runs in the typer's elimination sites, where the `requires` chain is
    /// complete regardless of source order; the loader only classifies. Returns `None`
    /// to fall back to the normal `remap_name` path:
    ///
    ///   - a head that is neither a type-parameter nor a sort (a namespace path);
    ///   - a sort-headed name that RESOLVES as a qualified name (`Enum.Entity` — a
    ///     legitimate qualified ref, never shadowed by projection classification).
    fn try_rigid_type_projection(
        &mut self,
        head_resolved: Symbol,
        head_name: &str,
        member_name: &str,
        span: SourceSpan,
    ) -> Option<node_occurrence::TypeChild> {
        let head_short = self.kb.resolve_sym(head_resolved).to_owned();
        let qn = self.kb.qualified_name_of(head_resolved).to_owned();
        let sort_qn = self.logical_sort_qn(&qn, &head_short).to_owned();
        // Rigid type-parameter head (`P.Key`): the head names a member sort whose
        // PARENT sort declares it as a type parameter — that parent is the sort whose
        // `requires` chain the eliminator consults. (NOT `is_type_param`, which reads
        // the current scope's own params and does not see the enclosing sort's member
        // params from an operation scope.) The parent-kind gate keeps the
        // `type_params_of_sort` scan off namespace-parented heads (every `Enum.Entity`
        // qualified ref).
        if let Some((parent_qn, _)) = sort_qn.rsplit_once('.') {
            if let Some(&decl_sort) = self.kb.symbols.by_qualified_name.get(parent_qn) {
                // The parent is the scope whose `requires` chain lends the subject its
                // members. A SORT parent's chain is the sort-level `requires` facts; an
                // OPERATION parent (an op type-param `getV.T`, WI-383) lends them through
                // the operation's own `requires` clause — `resolve_rigid_projection`
                // reads `OperationInfo.requires` for that case.
                if matches!(
                    self.kb.symbols.get(decl_sort),
                    SymbolDef::Resolved { kind: SymbolKind::Sort | SymbolKind::Operation, .. }
                ) && self.kb.type_params_of_sort(decl_sort).iter().any(|p| p == &head_short)
                {
                    // Subject = the param's LOGICAL registration (`ns.W.P`), so every
                    // spelling of `P.Key` hash-conses to one term regardless of which
                    // registration the head resolution landed on.
                    let subject_sym = *self
                        .kb
                        .symbols
                        .by_qualified_name
                        .get(sort_qn.as_str())
                        .unwrap_or(&head_resolved);
                    let member_sym = self.kb.intern(member_name);
                    let subject = self.kb.alloc(Term::Ref(subject_sym));
                    let proj = self.kb.make_rigid_projection(decl_sort, subject, member_sym);
                    // WI-429: record for the end-of-load formation sweep.
                    self.kb.rigid_projection_formations.push((proj, span));
                    return Some(node_occurrence::TypeChild::Ground(proj));
                }
            }
        }
        if !matches!(
            self.kb.symbols.get(head_resolved),
            SymbolDef::Resolved { kind: SymbolKind::Sort, .. }
        ) {
            return None;
        }
        // The canonical sort symbol for the (possibly inner self-named) head — the
        // symbol `type_params_of_sort` and the eliminator's `requires` lookup key on.
        let head_sort_sym = if sort_qn == qn {
            head_resolved
        } else {
            *self.kb.symbols.by_qualified_name.get(sort_qn.as_str())?
        };
        let head_declares_member =
            self.kb.type_params_of_sort(head_sort_sym).iter().any(|p| p == member_name);
        // Self-qualified member (`Storage.Key` INSIDE `Storage`'s own declaration): the
        // qualified spelling of the bare in-scope param `Key` — produce the same
        // sort-ref form the single-segment path builds for the bare name (design §5.3
        // bare-spec rule).
        if head_declares_member {
            if let ResolveResult::Found(member_resolved) =
                self.kb.symbols.resolve_in_scope(member_name, self.current_scope.raw())
            {
                let m_qn = self.kb.qualified_name_of(member_resolved).to_owned();
                if self
                    .logical_sort_qn(&m_qn, member_name)
                    .rsplit_once('.')
                    .is_some_and(|(parent, _)| parent == sort_qn)
                {
                    return Some(node_occurrence::TypeChild::Ground(
                        self.kb.make_sort_ref(member_resolved),
                    ));
                }
            }
            // WI-201: bare-spec-member sugar (carrier-direct, Reading A). We are in an
            // operation signature (`bare_spec_sugar` active) and `head.member` names a
            // declared type-param of the SPEC sort `head` with no carrier in scope (the
            // self-qualified check above did not fire). Desugar to a fresh op type-param
            // `?P` whose synthesized `requires <head>[member = ?P]` constrains it to be
            // the spec's `member`; the type at this position IS `?P`. Two refs to the
            // same `Spec.Member` in one signature share `?P` (dedup in the accumulator).
            //
            // ONLY for a spec (an interface — a Sort with no constructors): a
            // parameterized DATA sort (`Option`, `List`, a user enum) declares its
            // type-param too, but `Option.T` is a data param, not an associated spec
            // member to existentialize — it stays the loud conflation error, as before.
            if self.bare_spec_sugar.is_some() && !self.kb.sort_has_constructors(head_sort_sym) {
                let var = self.mint_bare_spec_carrier(head_sort_sym, member_name);
                return Some(node_occurrence::TypeChild::Ground(var));
            }
        } else {
            // A NON-param child of the head sort (`Outer.Inner` for a nested alias
            // sort, `Enum.Entity`) is a legitimate qualified CHILD reference, not a
            // projection — resolve it directly (the literal-joined check below cannot
            // see it: `by_qualified_name` holds the FULLY-qualified spelling).
            let child_qn = format!("{sort_qn}.{member_name}");
            if let Some(&child) = self.kb.symbols.by_qualified_name.get(&child_qn) {
                return Some(node_occurrence::TypeChild::Ground(self.kb.make_sort_ref(child)));
            }
        }
        // A sort-headed dotted name that RESOLVES under its written spelling
        // (scope-aware, or an import-established qualified name) is a legitimate
        // qualified ref — leave it to `remap_name`.
        let joined = format!("{head_name}.{member_name}");
        if !matches!(
            self.kb.symbols.resolve_in_scope(&joined, self.current_scope.raw()),
            ResolveResult::NotFound
        ) || self.kb.symbols.by_qualified_name.contains_key(&joined)
        {
            return None;
        }
        // Concrete / bare sort head (`MemStore.Key`, `Storage.Key` outside the sort):
        // subject = the sort itself (sort slot == var slot, the eliminator's
        // manifest-vs-rigid discriminator). The eliminator δ-grounds a manifest member
        // and LOUDLY rejects a bare-spec projection (the `T#K` guard).
        let member_sym = self.kb.intern(member_name);
        let subject = self.kb.alloc(Term::Ref(head_sort_sym));
        let proj = self.kb.make_rigid_projection(head_sort_sym, subject, member_sym);
        // WI-429: record for the end-of-load formation sweep.
        self.kb.rigid_projection_formations.push((proj, span));
        Some(node_occurrence::TypeChild::Ground(proj))
    }

    /// WI-201: mint (or reuse) the carrier-direct `?P` for a bare `Spec.Member` in the
    /// current operation signature, recording the synthesized `requires Spec[member =
    /// ?P]`. Deduped per `(spec, member)` within the one operation, so two occurrences
    /// of the same `Spec.Member` share `?P` (and a distinct operation, with its own
    /// accumulator, gets a distinct `?P`). Returns the `?P` var term — the type at the
    /// sugar position (design Reading A: the parameter IS the existential carrier, NOT a
    /// `?P.member` projection; the latter cannot infer `?P` from an argument when the
    /// projected member is itself the carrier, the WorkItemStore.State driving case).
    ///
    /// No symbol-table registration: the typer reads each var's surface name via
    /// `vid.name()` and treats EVERY var listed in `OperationInfo.type_params` as an
    /// inferable op type-parameter, so adding the minted var there (at the drain in
    /// `load_operation`) suffices. The synthesized `requires Spec[member = ?P]` is
    /// rebuilt from the recorded entry at the drain. Precondition:
    /// `self.bare_spec_sugar.is_some()`.
    fn mint_bare_spec_carrier(&mut self, spec: Symbol, member_name: &str) -> TermId {
        let member_sym = self.kb.intern(member_name);
        // WI-201 carrier-in-scope NARROWING: when the enclosing sort BINDS this spec
        // member to a CONCRETE carrier (`fact WorkItemStore[State = WIS]` / `provides …`),
        // the bare `Spec.Member` denotes that carrier — return it directly (no fresh
        // `?P`, no synthesized requires). The bindings were pre-scanned order-
        // independently in `load_sort_with_body` (already filtered to concrete,
        // unambiguous carriers, so a logic-var or conflicting binding falls through to a
        // fresh existential here rather than leaking an uninferable term).
        if let Some(&bound) = self.current_sort_carrier_bindings.get(&(spec, member_sym)) {
            return bound;
        }
        // Reuse an already-minted carrier for this `(spec, member)` in this signature.
        if let Some(sugar) = self.bare_spec_sugar.as_ref() {
            if let Some((_, var)) =
                sugar.minted.iter().find(|((s, m), _)| *s == spec && *m == member_sym)
            {
                return *var;
            }
        }
        // Fresh `?P`, named after the member so a diagnostic reads naturally
        // (`expected a type for 'State'`). The licensing `requires Spec[member = ?P]` is
        // synthesized from this entry at the drain.
        let vid = self.kb.fresh_var(member_sym);
        let var = self.kb.alloc(Term::Var(Var::Global(vid)));
        if let Some(sugar) = self.bare_spec_sugar.as_mut() {
            sugar.minted.push(((spec, member_sym), var));
        }
        var
    }

    /// WI-201: is `t` a CONCRETE carrier the bare-spec sugar may narrow to — a sort
    /// reference / application, never a logic var (a non-ground binding like `fact
    /// Spec[State = ?x]`). Narrowing to a var would leak a term that is NOT in the op's
    /// `type_params` and so cannot be inferred at a call; such a binding instead falls
    /// back to the fresh existential `?P`.
    fn is_concrete_carrier(&self, t: TermId) -> bool {
        matches!(self.kb.get_term(t), Term::Ref(_) | Term::Ident(_) | Term::Fn { .. })
    }

    /// WI-201: pre-scan a sort body's `provides` / `fact` items for spec-application
    /// bindings `Spec[… member = X …]`, mapping `(spec base sym, member sym)` → the
    /// bound value term `X`. Feeds the bare-spec sugar's carrier-in-scope narrowing
    /// (an impl that binds `WorkItemStore[State = WIS]` makes `WorkItemStore.State` ≡
    /// WIS inside its body). Read from the PARSE items before any operation in the body
    /// is loaded, so the narrowing does not depend on source order of fact-vs-op.
    /// Positional bindings (`fact Spec[WIS]`) are mapped to the spec's declared
    /// parameter order, mirroring [`Self::maybe_emit_fact_provides_info`].
    fn scan_sort_carrier_bindings(&mut self, items: &[Item]) -> HashMap<(Symbol, Symbol), TermId> {
        use crate::eval::value::Value;
        let mut out = HashMap::new();
        for item in items {
            // `fact Spec[…]` carries a parse-time term; `provides Spec[…]` a TypeExpr.
            let spec_term = match item {
                Item::Fact(f) => self.convert_term(f.term),
                Item::ProvidesClause(pc) => match self.sort_inst_to_value(&pc.spec) {
                    Value::Term { id: t, .. } => t,
                    // A denoted-bearing spec carries no concrete carrier to narrow to.
                    _ => continue,
                },
                _ => continue,
            };
            let (functor, pos_args, named_args) = match self.kb.get_term(spec_term) {
                Term::Fn { functor, pos_args, named_args } => {
                    (*functor, pos_args.clone(), named_args.clone())
                }
                _ => continue,
            };
            // Only a SPEC (an interface — a Sort with no constructors) lends carrier
            // members; skip a non-Sort fact term and a parameterized DATA sort (`List`,
            // `Option`, a user enum), matching the firing gate in the sugar itself.
            if !matches!(self.kb.kind_of(functor), Some(SymbolKind::Sort))
                || self.kb.sort_has_constructors(functor)
            {
                continue;
            }
            // Translate positional bindings to the spec's declared parameter order, so
            // `Spec[WIS]` and `Spec[Member = WIS]` record the same carrier; a named
            // binding for a slot wins over the positional one.
            let params = self.kb.type_params_of_sort(functor);
            let mut bindings: SmallVec<[(Symbol, TermId); 2]> = named_args.clone();
            for (i, val) in pos_args.iter().enumerate() {
                if let Some(name) = params.get(i) {
                    let key = self.kb.intern(name);
                    if !bindings.iter().any(|(s, _)| *s == key) {
                        bindings.push((key, *val));
                    }
                }
            }
            for (key, val) in bindings {
                // Narrow ONLY to a concrete carrier (never a logic var / placeholder),
                // and only when UNAMBIGUOUS: a second fact binding the same `(spec,
                // member)` to a different carrier drops the entry, so the sugar mints a
                // fresh existential (and the duplicate-provider coherence check surfaces
                // the real error) rather than silently picking a source-order winner.
                if !self.is_concrete_carrier(val) {
                    continue;
                }
                use std::collections::hash_map::Entry;
                match out.entry((functor, key)) {
                    Entry::Occupied(e) => {
                        if *e.get() != val {
                            e.remove();
                        }
                    }
                    Entry::Vacant(e) => {
                        e.insert(val);
                    }
                }
            }
        }
        out
    }

    fn type_expr_to_child(
        &mut self,
        ty: &TypeExpr,
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> node_occurrence::TypeChild {
        // WI-429: everything beneath here is TYPE position — an unresolvable
        // Capitalized dotted name is load-blocking (`remap_name`'s
        // `UnresolvedTypeName` arm). Save/restore (not just set) so a value
        // sub-context a future arm introduces can opt back out.
        let saved_type_pos = std::mem::replace(&mut self.in_type_position, true);
        let child = self.type_expr_to_child_inner(ty, span, owner);
        self.in_type_position = saved_type_pos;
        child
    }

    fn type_expr_to_child_inner(
        &mut self,
        ty: &TypeExpr,
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> node_occurrence::TypeChild {
        match ty {
            TypeExpr::Simple(name) => {
                // WI-341: a callback arrow's own param (`a` in `Modify[a]`,
                // in scope only while loading that callback param's arrow type)
                // resolves to its `CallbackParam` place — minted as a
                // `Value::Node` `denoted` occurrence (not a hash-consed `Ref`).
                if name.segments.len() == 1 && !self.arrow_binder_scope.is_empty() {
                    let nm = self.parsed.symbols.name(name.segments[0]);
                    if let Some(&place) = self.arrow_binder_scope.get(nm) {
                        return node_occurrence::TypeChild::Node(
                            self.kb.make_denoted_occ_ref(place, span, owner),
                        );
                    }
                }
                // WI-376: a MULTI-segment name whose HEAD resolves to a VALUE
                // (param / local / field / op-result) is an expression-carried type
                // projection `s.T` / `s.Sort` — the type-member sibling of the
                // single-segment `denoted` value-in-type below. Classify it HERE,
                // before `remap_name`, which would otherwise join the segments
                // (`"s.T"`) and raise the load-blocking `UnresolvedTypeName`
                // (WI-429). A qualified sort ref (`anthill.prelude.List`, head =
                // namespace) is NOT a value head, so it falls through to the
                // normal sort-ref path.
                if name.segments.len() >= 2 {
                    if let Some(child) = self.try_expr_carried_projection(name, span, owner) {
                        return child;
                    }
                    // WI-302 (proposal 027.1): a value FIELD-access path (`result.a`,
                    // `c.contents`, lowercase last segment off a value head) is a
                    // value-in-type DENOTED place — the compound peer of the
                    // single-segment `denoted` below. Classify it before `remap_name`,
                    // which would otherwise join the segments into an unresolvable
                    // `"c.contents"` and emit a stray `unresolved name`.
                    if let Some(child) = self.try_denoted_value_path(name, span, owner) {
                        return child;
                    }
                }
                let sort_sym = self.remap_name(name);
                let short_name = self.kb.resolve_sym(sort_sym).to_owned();
                // A type-param name is a ground logic Var (no denoted) — build it
                // via the shared `type_param_var` helper (NOT `type_expr_to_value`,
                // which this fn must not call, see the wrapper note on it).
                if self.kb.symbols.is_type_param(self.current_scope.raw(), &short_name) {
                    return node_occurrence::TypeChild::Ground(
                        self.type_param_var(sort_sym, &short_name),
                    );
                }
                // WI-302/WI-313: a name resolving to a VALUE in a type slot is
                // value-in-type (`Modify[c]`) — the `denoted` source. Mint it as
                // a `Value::Node` occurrence rather than the ground `make_denoted`.
                // Shared value-place set + a zero-arg `Operation` (the WI-313
                // ambient-KB accessor `Modify[op]`, value-producing) — the one kind
                // the compound-path heads omit (a field off an op name is not a place).
                let is_value = self.symbol_is_value_place(sort_sym)
                    || matches!(
                        self.kb.symbols.get(sort_sym),
                        SymbolDef::Resolved { kind: SymbolKind::Operation, .. }
                    );
                if is_value {
                    node_occurrence::TypeChild::Node(
                        self.kb.make_denoted_occ_ref(sort_sym, span, owner),
                    )
                } else {
                    node_occurrence::TypeChild::Ground(self.kb.make_sort_ref(sort_sym))
                }
            }
            TypeExpr::Parameterized { name, bindings } => {
                let sort_sym = self.remap_name(name);
                let base_term = self.kb.make_sort_ref(sort_sym);
                // Same positional→declared-param-name mapping for both the node
                // and the ground hash-consed form, so a label's binding
                // symbols match across the two carriers (the display-name
                // comparison in the op-boundary check relies on this).
                let declared_params = self.kb.type_params_of_sort(sort_sym);
                // WI-709: the arguments must FIT the sort's declared params — an
                // undeclared name or an over-applied positional is load-blocking, decided
                // by the same rule the VALUE position (WI-707) decides it by, so one
                // written type cannot mean two things. Reported once here; the binding
                // loop below then proceeds (a stray name still lands in the term, but the
                // load already failed, so nothing downstream reads it).
                let named_syms: SmallVec<[Symbol; 2]> = bindings
                    .iter()
                    .filter_map(|b| b.param.as_ref().map(|p| self.reintern(p.last())))
                    .collect();
                let positional_count = bindings.len() - named_syms.len();
                if let Err(problem) = self.kb.check_sort_type_args(
                    sort_sym,
                    &declared_params,
                    &named_syms,
                    positional_count,
                ) {
                    let detail = problem.describe(&self.kb, sort_sym);
                    self.errors
                        .push(LoadError::InvalidTypeArgument { detail, span: Some(span.span) });
                }
                let mut child_bindings: Vec<(Symbol, node_occurrence::TypeChild)> = Vec::new();
                let mut positional_index: usize = 0;
                let mut any_node = false;
                for b in bindings {
                    let bound_child = self.type_expr_to_child(&b.bound, span, owner);
                    if matches!(bound_child, node_occurrence::TypeChild::Node(_)) {
                        any_node = true;
                    }
                    let param_sym = if let Some(p) = &b.param {
                        Some(self.reintern(p.last()))
                    } else {
                        // A positional binds the next declared param NOT already given by
                        // name — eval's rule (`finish_sort_type`), so `Map[K = K1, V1]`
                        // binds `V` rather than re-binding `K` to a second value (which
                        // would build a duplicate-key type term, a shape the evaluated
                        // spelling of the same type never produces).
                        loop {
                            match declared_params.get(positional_index) {
                                Some(param_name) => {
                                    let param_name = param_name.clone();
                                    positional_index += 1;
                                    let sym = self.kb.intern(&param_name);
                                    if !named_syms.contains(&sym) {
                                        break Some(sym);
                                    }
                                }
                                // Over-applied — already reported above.
                                None => break None,
                            }
                        }
                    };
                    if let Some(sym) = param_sym {
                        child_bindings.push((sym, bound_child));
                    }
                }
                if any_node {
                    node_occurrence::TypeChild::Node(self.kb.make_parameterized_occ(
                        node_occurrence::TypeChild::Ground(base_term),
                        child_bindings,
                        span,
                        owner,
                    ))
                } else {
                    // No denoted binding ⇒ assemble the hash-consed parameterized
                    // term from the ground children already built (NOT a second
                    // structural walk; same `base_term` + the same
                    // positional→param-name mapping ⇒ the ground hash-consed form).
                    let ground_bindings: Vec<(Symbol, TermId)> = child_bindings
                        .into_iter()
                        .map(|(s, c)| match c {
                            node_occurrence::TypeChild::Ground(t) => (s, t),
                            node_occurrence::TypeChild::Node(_) => unreachable!("checked !any_node"),
                        })
                        .collect();
                    node_occurrence::TypeChild::Ground(
                        self.kb.make_parameterized_type(base_term, &ground_bindings),
                    )
                }
            }
            TypeExpr::Arrow { params, return_type, effects } => {
                use node_occurrence::TypeChild;
                // WI-341: a callback arrow whose effect is denoted-bearing
                // (`Modify[a]`) becomes a `Value::Node` arrow so the occurrence is
                // CARRIED, not re-grounded. The binder scope applies only to the
                // EFFECT labels (a self-referential `Modify[a]`); suspend it for
                // the param/return TYPE positions (mirror `type_expr_to_child`),
                // restore it for the effects.
                let saved = std::mem::take(&mut self.arrow_binder_scope);
                let param_child = if params.len() == 1 {
                    self.type_expr_to_child(&params[0].1, span, owner)
                } else {
                    let mut fields: Vec<(Symbol, TypeChild)> = Vec::new();
                    let mut any = false;
                    for (i, (name, p)) in params.iter().enumerate() {
                        let key = match name {
                            Some(s) => {
                                let nm = self.parsed.symbols.name(*s).to_owned();
                                self.kb.intern(&nm)
                            }
                            None => self.kb.intern(&format!("_{}", i + 1)),
                        };
                        let c = self.type_expr_to_child(p, span, owner);
                        any |= matches!(c, TypeChild::Node(_));
                        fields.push((key, c));
                    }
                    if any {
                        TypeChild::Node(self.kb.make_named_tuple_occ(fields, span, owner))
                    } else {
                        let ground: Vec<(Symbol, TermId)> = fields
                            .into_iter()
                            .map(|(k, c)| match c {
                                TypeChild::Ground(t) => (k, t),
                                TypeChild::Node(_) => unreachable!("checked !any"),
                            })
                            .collect();
                        TypeChild::Ground(self.kb.make_named_tuple_type(&ground))
                    }
                };
                let result_child = self.type_expr_to_child(return_type, span, owner);
                self.arrow_binder_scope = saved;
                let effect_children: Vec<TypeChild> = effects
                    .iter()
                    .map(|e| self.type_expr_to_child(e, span, owner))
                    .collect();
                // WI-440 (row-openness decision): an absence-only annotation
                // (`@ -Modify[x]`) stays a CLOSED row carrying the lacks atom —
                // openness is written EXPLICITLY with a row variable
                // (`@ {Eff, -Modify[x]}`, `Eff` an op type param the HOF also
                // declares via `effects Eff`). An implicit fresh tail was tried
                // and reverted: the minted var is unnameable, so a HOF APPLYING
                // the callback surfaced an "undeclared effect ?ρ" it had no
                // syntax to declare.
                let any_node = matches!(param_child, TypeChild::Node(_))
                    || matches!(result_child, TypeChild::Node(_))
                    || effect_children.iter().any(|c| matches!(c, TypeChild::Node(_)));
                if !any_node {
                    // Fully ground arrow — assemble the hash-consed term from the
                    // children already built (no second structural walk;
                    // the signature never re-grounds through that path).
                    let ground = |c: TypeChild| match c {
                        TypeChild::Ground(t) => t,
                        TypeChild::Node(_) => unreachable!("checked !any_node"),
                    };
                    let param_t = ground(param_child);
                    let result_t = ground(result_child);
                    let effect_ts: Vec<TermId> = effect_children.into_iter().map(ground).collect();
                    return TypeChild::Ground(self.kb.make_arrow_type(param_t, result_t, &effect_ts));
                }
                // WI-377: fold the effect children into an `effects_rows`
                // occurrence via the shared absent-aware helper. The earlier
                // hand-rolled fold here wrapped EVERY child in `present(…)`,
                // double-wrapping a `-E` lacks-atom (already an `absent(…)` atom
                // from the `EffectAbsent` arm) into `present(absent(E))`; the
                // helper keeps absent atoms bare.
                let effects_child = self.fold_effect_row_occ(effects, effect_children, span, owner);
                TypeChild::Node(
                    self.kb
                        .make_arrow_occ(param_child, result_child, effects_child, span, owner),
                )
            }
            TypeExpr::Tuple(fields) => {
                use node_occurrence::TypeChild;
                // Mirror the Arrow multi-param branch: lower each field via the
                // carrier-agnostic child path; any `Node` field poisons the tuple
                // to a `Value::Node` named_tuple, else assemble the hash-consed
                // term (the ground hash-consed form).
                let mut children: Vec<(Symbol, TypeChild)> = Vec::new();
                let mut any_node = false;
                for (sym, fty) in fields {
                    let key = self.reintern(*sym);
                    let c = self.type_expr_to_child(fty, span, owner);
                    any_node |= matches!(c, TypeChild::Node(_));
                    children.push((key, c));
                }
                if any_node {
                    TypeChild::Node(self.kb.make_named_tuple_occ(children, span, owner))
                } else {
                    let ground: Vec<(Symbol, TermId)> = children
                        .into_iter()
                        .map(|(k, c)| match c {
                            TypeChild::Ground(t) => (k, t),
                            TypeChild::Node(_) => unreachable!("checked !any_node"),
                        })
                        .collect();
                    TypeChild::Ground(self.kb.make_named_tuple_type(&ground))
                }
            }
            TypeExpr::Variable { term_id, descriptions } => {
                // A logic Var is always ground (no denoted) — convert the term
                // and emit its descriptions, yielding the ground hash-consed form.
                let kb_id = self.convert_term(*term_id);
                for desc_text in descriptions {
                    self.emit_desc_fact(kb_id, desc_text, self.current_scope);
                }
                node_occurrence::TypeChild::Ground(kb_id)
            }
            TypeExpr::Denoted(t) => {
                // WI-342: value-in-type literal (`3` in `Vector[Int64, 3]` / `g[3]`)
                // — carried as a `Value::Node` `denoted` occurrence whose value is
                // the literal as an `Expr::Const` occurrence (the occurrence-form
                // peer of `make_denoted(Const(lit))`). This is THE site that
                // retires the loader's last live `make_denoted`: a denoted now
                // rides on the non-hash-consed carrier.
                let value_term = self.convert_term(*t);
                let value_occ = self.value_term_to_occ(value_term, span, owner);
                node_occurrence::TypeChild::Node(self.kb.make_denoted_occ(value_occ, span, owner))
            }
            TypeExpr::EffectAbsent(inner) => {
                // `-E` lacks-atom: ground inner ⇒ hash-consed `absent` term
                // (mirror `type_expr_to_child`); a denoted-bearing inner ⇒ the
                // occurrence `absent` form (carries the poison).
                // WI-440: flag the inner lowering so an unresolved name there
                // is a load-blocking error (a vacuous absence), not a warning.
                let saved_absence = std::mem::replace(&mut self.in_effect_absence, true);
                let inner_child = self.type_expr_to_child(inner, span, owner);
                self.in_effect_absence = saved_absence;
                match inner_child {
                    node_occurrence::TypeChild::Ground(t) => {
                        node_occurrence::TypeChild::Ground(self.kb.make_effect_expression_absent(t))
                    }
                    node_occurrence::TypeChild::Node(n) => node_occurrence::TypeChild::Node(
                        self.kb.make_absent_occ(node_occurrence::TypeChild::Node(n), span, owner),
                    ),
                }
            }
            // WI-375: a WRITTEN effect-row in a type-argument value slot
            // (`Stream[E = {}]` / `Stream[E = {Modify[c]}]`) → the KB
            // `effects_rows(EffectExpression)` Type (the WI-320 bridge).
            TypeExpr::EffectRow(effects) => self.lower_effect_row(effects, span, owner),
            // WI-478 (proposal 048): a guarded effect `E :- guard` → the
            // `guarded(label, guard: List[reflect.Term])` EffectExpression atom.
            // The guard goals convert in the CURRENT (op) scope, so param refs
            // (`eq(b, 0)`) resolve. A GROUND label hash-conses the whole atom (term
            // form); a denoted-bearing label poisons it to the node form, the guard
            // goals carried as `Value`s. Like `EffectAbsent`, this arm produces a
            // COMPLETE EffectExpression atom — the row folders carry it BARE (never
            // wrap it in `present`).
            TypeExpr::EffectGuarded { label, guard } => {
                // WI-552: canonicalize the guard's param refs to var_ref at the
                // producer (the guard goals resolve in the current op scope, so a
                // `Modify[c] :- eq(c, 0)` guard's `c` is a signature place) — the
                // guard then carries the binder as a variable and the discharge-time
                // normalize pass is retired.
                let guard_terms: Vec<TermId> = guard
                    .iter()
                    .map(|g| {
                        let t = self.convert_term(*g);
                        self.var_ref_signature_places(t)
                    })
                    .collect();
                let label_child = self.type_expr_to_child(label, span, owner);
                match label_child {
                    node_occurrence::TypeChild::Ground(label_t) => {
                        let guard_list = self.kb.build_list(&guard_terms);
                        node_occurrence::TypeChild::Ground(
                            self.kb.make_effect_expression_guarded(label_t, guard_list),
                        )
                    }
                    node_occurrence::TypeChild::Node(label_o) => {
                        let guard_values: Vec<crate::eval::value::Value> = guard_terms
                            .into_iter()
                            .map(crate::eval::value::Value::term)
                            .collect();
                        let guard_value = build_value_list(self.kb, guard_values);
                        node_occurrence::TypeChild::Node(self.kb.make_guarded_occ(
                            node_occurrence::TypeChild::Node(label_o),
                            guard_value,
                            span,
                            owner,
                        ))
                    }
                }
            }
        }
    }

    /// WI-375: lower a WRITTEN effect-row (`{}`, `{Modify[c]}`, `{A, -B}`, …)
    /// to the KB `effects_rows(EffectExpression)` Type. A fully-ground row
    /// (bare labels / `Modify[Int64]` / `-E`, no value-in-type) assembles the
    /// canonical hash-consed term via [`build_canonical_effects_rows`] — which
    /// wraps each bare label in `present(…)`, keeps pre-built `absent(…)`
    /// atoms, sorts, and dedups. A denoted-bearing label (`Modify[c]`, `c` a
    /// value) poisons the row to the occurrence form via the shared
    /// [`fold_effect_row_occ`](Self::fold_effect_row_occ) — the same fold the
    /// `Arrow` arm uses — so the value-in-type occurrence is CARRIED, not
    /// re-grounded.
    ///
    /// [`build_canonical_effects_rows`]: KnowledgeBase::build_canonical_effects_rows
    fn lower_effect_row(
        &mut self,
        effects: &[TypeExpr],
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> node_occurrence::TypeChild {
        use node_occurrence::TypeChild;
        let effect_children: Vec<TypeChild> = effects
            .iter()
            .map(|e| self.type_expr_to_child(e, span, owner))
            .collect();
        let any_node = effect_children.iter().any(|c| matches!(c, TypeChild::Node(_)));
        if !any_node {
            // Fully ground row — `build_canonical_effects_rows` owns the
            // present/absent wrapping + canonical ordering (the same call the
            // ground `Arrow` arm reaches through `make_arrow_type`).
            let effect_ts: Vec<TermId> = effect_children
                .into_iter()
                .map(|c| match c {
                    TypeChild::Ground(t) => t,
                    TypeChild::Node(_) => unreachable!("checked !any_node"),
                })
                .collect();
            return TypeChild::Ground(self.kb.build_canonical_effects_rows(&effect_ts));
        }
        // Denoted-bearing — fold into an `effects_rows` occurrence via the
        // shared absent-aware helper (the same fold the `Arrow` arm uses).
        self.fold_effect_row_occ(effects, effect_children, span, owner)
    }

    /// WI-377: fold an effect list into an `effects_rows(EffectExpression)`
    /// OCCURRENCE (the denoted-bearing `Value::Node` form), shared by the
    /// written-row [`lower_effect_row`](Self::lower_effect_row) and the `Arrow`
    /// arm's effects fold. Each element's pre-lowered `child` is wrapped in
    /// `present(…)` UNLESS the source `TypeExpr` is a `-E` lacks-atom
    /// (`EffectAbsent`) — which is already an `absent(…)` atom from the
    /// `EffectAbsent` arm and must be carried bare (wrapping it would yield the
    /// malformed `present(absent(E))`). Source order, not canonicalized:
    /// occurrences are not hash-consed, so the dedup-canonical form does not
    /// apply (as for arrows). `effects` and `effect_children` are zipped, so
    /// they MUST be the same length and order (the callers build `effect_children`
    /// by `type_expr_to_child`-mapping `effects`).
    fn fold_effect_row_occ(
        &mut self,
        effects: &[TypeExpr],
        effect_children: Vec<node_occurrence::TypeChild>,
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> node_occurrence::TypeChild {
        use node_occurrence::TypeChild;
        let mut row = TypeChild::Node(self.kb.make_empty_row_occ(span, owner));
        for (e, child) in effects.iter().zip(effect_children.into_iter()).rev() {
            // WI-440/441: a row-tail VARIABLE element — an op-level row param
            // (`@ {Eff, -Modify[x]}`, a bare `Var`) or a SORT-level row param
            // (lowered as `Ref(S.E)`, resolved to its alias Var) — folds as
            // `open(?Eff)`; wrapping it in `present(…)` would decompose the
            // VAR as a present LABEL, losing the tail (the ground path's
            // `build_canonical_effects_rows` applies the same rule).
            let row_var = match &child {
                TypeChild::Ground(t) => self.kb.row_tail_var_of(*t),
                TypeChild::Node(_) => None,
            };
            // WI-478: a guarded atom (like an `EffectAbsent` `absent(…)`) is already
            // a COMPLETE EffectExpression atom from `type_expr_to_child` — carry it
            // bare; wrapping it in `present(…)` would yield malformed `present(guarded(…))`.
            let atom = if matches!(e, TypeExpr::EffectAbsent(_) | TypeExpr::EffectGuarded { .. }) {
                child
            } else if let Some(v) = row_var {
                TypeChild::Node(self.kb.make_open_occ(TypeChild::Ground(v), span, owner))
            } else {
                TypeChild::Node(self.kb.make_present_occ(child, span, owner))
            };
            row = TypeChild::Node(self.kb.make_merge_occ(atom, row, span, owner));
        }
        TypeChild::Node(self.kb.make_effects_rows_occ(row, span, owner))
    }

    /// WI-391: lower a spec BINDING VALUE (the `Int` in `provides Spec[T = Int]`, or a
    /// positional binding) to its CANONICAL type shape. A bare sort lowers to `Ref(S)` —
    /// the one extractable bare-sort shape (`type_head` classifies a no-arg `Fn{S}` as
    /// MALFORMED → `TypeExtractor::Error`; only `Ref(S)` is a bare sort) and byte-identical
    /// to the `fact`-head path (parse `convert_type_value` → `Ref(S)`), never the
    /// `name_to_sort_term` nullary `Fn`. This is the binding-VALUE counterpart of
    /// [`sort_inst_to_value`]'s spec-IDENTITY lowering, whose bare-`Simple` arm must stay
    /// the `Fn{S}` functor the spec readers (`unwrap_spec_view`) require — the two slots
    /// carry the same syntax (`Spec`) but different roles. Whether `S` is a type-PARAM (a
    /// dispatch wildcard) or a CONCRETE sort is recovered DOWNSTREAM from the symbol's kind
    /// (`is_sort_param_symbol`, consulted by `dispatch_values_match`), never from the lowered
    /// shape, so one canonical `Ref` serves both. Normalizing here — at the producer — is
    /// the "normalize early" point that lets type-position consumers drop the late
    /// `Fn{S}→Ref(S)` patch (`normalize_ground_leaf`); subsumes WI-387 (which aligned only
    /// the `T = T` param half). A parameterized / effect-row / other binding delegates to
    /// [`sort_inst_to_value`] unchanged.
    fn sort_binding_to_value(&mut self, ty: &TypeExpr) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        match ty {
            TypeExpr::Simple(name) => {
                let sort_sym = self.remap_name(name);
                Value::term(self.kb.make_sort_ref(sort_sym))
            }
            // WI-600: a NESTED parameterized binding VALUE (`Element = Pair[A = K, B
            // = V]`) is lowered to the PLAIN parameterized term `Fn{Pair, named}` —
            // NOT a `reflect.SortView` wrapper. Only the OUTER spec view is a
            // `SortView` (assembled by the top-level `sort_inst_to_value` /
            // `maybe_emit_fact_provides_info`); a nested type argument is an ordinary
            // type, so carrier grounding (`substitute_carrier_params`) grounds and
            // compares it against a user-written `Pair[…]` (also a plain `Fn`)
            // directly, with no SortView→Fn rebuild. The leaves stay canonical `Ref`s
            // (the dispatch matcher's `impl_param_ref` wildcard contract, WI-387).
            // A denoted-bearing child (a value-in-type) can't ride a hash-consed
            // `Fn`, so that exotic case keeps the faithful `SortView` `Value::Entity`
            // carrier via `assemble_sort_view_value` — matching this fn's twin,
            // `canonicalize_fact_binding_value`, so the fact / provides emissions
            // stay byte-identical (WI-449).
            TypeExpr::Parameterized { name, bindings } => {
                let base_sym = self.remap_name(name);
                let declared_params = self.kb.type_params_of_sort(base_sym);
                // Explicit named bindings first, then positionals mapped onto the
                // declared params in order — matching `canonicalize_fact_binding_value`
                // (its input `Fn` lists named_args before pos_args), so the fact and
                // provides emissions stay byte-identical (WI-449). A double-bind or an
                // overflow positional diverts to `pos`, which `assemble_binding_value`
                // preserves (via the `SortView` carrier) rather than dropping — the
                // loud-over-silent rule.
                let mut named: Vec<(Symbol, Value)> = Vec::new();
                let mut positionals: Vec<Value> = Vec::new();
                for b in bindings {
                    let bound = self.sort_binding_to_value(&b.bound);
                    match &b.param {
                        Some(p) => named.push((self.reintern(p.last()), bound)),
                        None => positionals.push(bound),
                    }
                }
                let mut pos: Vec<Value> = Vec::new();
                let mut positional_index: usize = 0;
                for bound in positionals {
                    match declared_params.get(positional_index) {
                        Some(pn) => {
                            positional_index += 1;
                            let sym = self.kb.intern(pn);
                            if named.iter().any(|(s, _)| *s == sym) {
                                pos.push(bound);
                            } else {
                                named.push((sym, bound));
                            }
                        }
                        None => pos.push(bound),
                    }
                }
                self.assemble_binding_value(base_sym, named, pos)
            }
            _ => self.sort_inst_to_value(ty),
        }
    }

    /// WI-366 — lower a `requires` / `provides` spec to a sort instantiation
    /// (`SortView`), as a carrier-agnostic [`Value`](crate::eval::value::Value): a
    /// fully-ground spec rides as `Value::Term` (the hash-consed `SortView` / sort
    /// term); a spec with a denoted-bearing binding (a value-in-type — `Modify[c]`,
    /// `Vector[Int64, 3]`) rides as a
    /// `Value::Entity` `SortView` carrying the `Value::Node` binding, so the value-
    /// in-type is CARRIED (the `SortRequiresInfo` / `SortProvidesInfo` fact becomes
    /// a value fact) rather than re-grounded via `make_denoted`.
    fn sort_inst_to_value(&mut self, ty: &TypeExpr) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        match ty {
            TypeExpr::Simple(name) => {
                // WI-387: a type-param binding value (the `T` in `provides
                // Stream[T = T]`) must lower to a `Ref(param)` — the SAME shape
                // the `fact`-head path (`maybe_emit_fact_provides_info` over
                // `convert_term`) emits — not the nullary `Fn` `name_to_sort_term`
                // builds. Only `Ref`/`Ident` is recognized as a dispatch type-param
                // WILDCARD (`impl_param_ref`); a nullary `Fn` scores CONCRETE
                // specificity, so a `provides`-clause provider out-ranks an
                // equivalent `fact` provider and breaks carrier-less `Ambiguous`
                // dispatch (wi210). A universal `provides Spec[T = T]` IS a wildcard
                // provision, exactly like `fact Spec[T = T]` — the two must emit
                // structurally identical `SortProvidesInfo` bindings.
                //
                // NOTE this arm is reached for BOTH the whole spec when it is a bare
                // `provides Spec` (the spec-IDENTITY slot, which the spec readers need
                // as the `Fn{Spec}` functor) AND a nested binding VALUE. A concrete
                // bare sort stays the `Fn{S}` functor here; the binding-value position
                // canonicalizes to `Ref(S)` separately (WI-391, `sort_binding_to_value`).
                let sort_sym = self.remap_name(name);
                let short_name = self.kb.resolve_sym(sort_sym).to_owned();
                if self.kb.symbols.is_type_param(self.current_scope.raw(), &short_name) {
                    Value::term(self.kb.make_sort_ref(sort_sym))
                } else {
                    Value::term(self.name_to_sort_term(name))
                }
            }
            TypeExpr::Parameterized { name, bindings } => {
                let name_term = self.name_to_sort_term(name);
                let mut pos: Vec<Value> = vec![Value::term(name_term)];
                let mut named: Vec<(Symbol, Value)> = Vec::new();
                // Positional bindings map to the base sort's declared type
                // parameters in declaration order — the SAME mapping
                // `type_expr_to_child` applies to plain type expressions — so a
                // `provides Stream[T, {}]` and `provides Stream[T = T, E = {}]`
                // build structurally identical NAMED `SortView` bindings. The
                // provider / requires / dispatch readers (`unwrap_spec_view`)
                // read NAMED args only; a positional binding left in `pos` is
                // invisible to them, so without this mapping a positional spec
                // clause silently loses its bindings (a pure `provides` would
                // drop its `E = {}` and the carrier would stop being admissible
                // as the spec).
                let base_sym = self.remap_name(name);
                let declared_params = self.kb.type_params_of_sort(base_sym);
                let mut positional_index: usize = 0;
                for b in bindings {
                    let bound = self.sort_binding_to_value(&b.bound);
                    let param_sym = match &b.param {
                        Some(p) => Some(self.reintern(p.last())),
                        None if positional_index < declared_params.len() => {
                            let param_name = declared_params[positional_index].clone();
                            positional_index += 1;
                            Some(self.kb.intern(&param_name))
                        }
                        None => None,
                    };
                    match param_sym {
                        Some(sym) => named.push((sym, bound)),
                        None => pos.push(bound),
                    }
                }
                self.assemble_sort_view_value(pos, named)
            }
            _ => self.type_expr_to_value(ty),
        }
    }

    /// Assemble a `SortView` carrier from its positional slot (the base sort's name
    /// term in `pos[0]`, plus any binding left unmapped) and its named bindings,
    /// choosing the faithful representation: a `Value::Entity` when ANY binding
    /// carries a non-`Term` value (a denoted `Node`, a nested value `SortView` —
    /// information a hash-consed `Term` cannot hold), else the all-ground
    /// hash-consed `Value::Term(SortView…)`. The single decision point shared by
    /// [`sort_inst_to_value`] (the `provides` / `requires` path) and
    /// [`canonicalize_fact_binding_value`] (the fact path), so the two emit
    /// BYTE-IDENTICAL specs and a binding's value is never silently dropped.
    fn assemble_sort_view_value(
        &mut self,
        pos: Vec<crate::eval::value::Value>,
        mut named: Vec<(Symbol, crate::eval::value::Value)>,
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        let sort_view_sym = self.kb.resolve_symbol("anthill.reflect.SortView");
        // Canonicalize the named bindings by SYMBOL INDEX — `kb.alloc` hash-conses
        // a `Term::Fn` with its `named_args` AS GIVEN (unlike the `make_*`
        // builders, it does not sort), so two specs that differ only in written
        // field order (`Spec[a = …, b = …]` vs `Spec[b = …, a = …]`) would
        // otherwise lower to DISTINCT spec views and read as a false coherence
        // ambiguity (WI-431 rule 2). Sorting here makes the spec view
        // order-insensitive for every caller (fact + provides), so the WI-449
        // byte-identity holds regardless of source order.
        //
        // WI-498: this index sort is DELIBERATE and does NOT route through the
        // `make_entity_term` / `canonicalize_record_named_args` funnel (unlike the
        // persistence term builders). The named keys here are the viewed spec's
        // TYPE-PARAM bindings (`T`, `E` of `Spec[T = …, E = …]`), not declared
        // fields of the `SortView` entity (whose `entity_field_names` are a fixed
        // reflect schema that does not contain `T`/`E`). Funneling would sort the
        // type-param bindings against SortView's own field list — all unmatched,
        // collapsing to `usize::MAX` and a non-index order — breaking the WI-449
        // byte-identity. Index order is the right canonical key for this slot.
        named.sort_by_key(|(s, _)| s.index());
        // A spec is ground iff every binding is ground; any non-`Term` binding
        // poisons the whole spec to a value carrier (no information lost).
        let any_value = pos.iter().any(|v| !matches!(v, Value::Term { .. }))
            || named.iter().any(|(_, v)| !matches!(v, Value::Term { .. }));
        if any_value {
            Value::Entity {
                functor: sort_view_sym,
                pos: std::rc::Rc::from(pos),
                named: std::rc::Rc::from(named),
            }
        } else {
            let pos_args: SmallVec<[TermId; 4]> = pos
                .iter()
                .map(|v| v.expect_term())
                .collect();
            let named_args: SmallVec<[(Symbol, TermId); 2]> = named
                .iter()
                .map(|(s, v)| (*s, v.expect_term()))
                .collect();
            Value::term(self.kb.alloc(Term::Fn {
                functor: sort_view_sym,
                pos_args,
                named_args,
            }))
        }
    }

    /// Load items (top-level or within a domain), tracking scope.
    fn load_items(&mut self, items: &[Item], domain: Option<TermId>) {
        let prev_scope = self.current_scope;
        let domain = domain.unwrap_or_else(|| self.kb.make_name_term("_global"));
        self.current_scope = domain;

        // WI-233: per-item-kind timing/count, gated by
        // ANTHILL_ITEM_TIMING=1. Aggregated across all `load_items`
        // invocations into thread-local counters; printed by the
        // outermost caller at end-of-pass.
        let timing = std::env::var("ANTHILL_ITEM_TIMING").map(|v| v == "1").unwrap_or(false);

        for item in items {
            let t0 = if timing { Some(std::time::Instant::now()) } else { None };
            let kind = match item {
                Item::Namespace(n) => { self.load_namespace(n); "Namespace" }
                Item::AbstractSort(s) => { self.load_abstract_sort(s, domain); "AbstractSort" }
                Item::SortWithBody(s) => { self.load_sort_with_body(s, domain); "SortWithBody" }
                Item::Rule(r) => { self.load_rule(r, domain); "Rule" }
                Item::Operation(o) => { self.load_operation(o, domain); "Operation" }
                Item::Const(c) => { self.load_const(c, domain); "Const" }
                Item::RequiresDecl(r) => { self.load_requires_decl(r, domain); "RequiresDecl" }
                Item::Entity(e) => { self.load_entity(e, domain); "Entity" }
                Item::Fact(f) => { self.load_fact(f, domain); "Fact" }
                Item::Constraint(c) => { self.load_constraint(c, domain); "Constraint" }
                Item::OperationBlock(ob) => {
                    for op in &ob.entries {
                        self.load_operation(op, domain);
                    }
                    "OperationBlock"
                }
                Item::RuleBlock(rb) => {
                    for rule in &rb.entries {
                        self.load_rule(rule, domain);
                    }
                    "RuleBlock"
                }
                Item::Describe(d) => { self.load_describe(d, domain); "Describe" }
                Item::Proof(p) => { self.load_proof(p, domain); "Proof" }
                Item::ProvidesClause(pc) => { self.load_provides_clause(pc, domain); "ProvidesClause" }
                Item::ProvidesBlock(pb) => { self.load_provides_block(pb, domain); "ProvidesBlock" }
            };
            if let Some(t0) = t0 {
                let dt = t0.elapsed();
                ITEM_TIMINGS.with(|m| {
                    let mut m = m.borrow_mut();
                    let entry = m.entry(kind).or_insert((0u32, std::time::Duration::ZERO));
                    entry.0 += 1;
                    entry.1 += dt;
                });
            }
        }

        self.current_scope = prev_scope;
    }

    fn load_namespace(&mut self, n: &Namespace) {
        let ns_term = self.name_to_sort_term(&n.name);
        let ns_sort = self.kb.make_name_term("Namespace");

        // Assert namespace as a fact
        self.kb.assert_fact(ns_term, ns_sort, ns_term, None);

        // Set scope to namespace for member resolution
        let prev_scope = self.current_scope;
        self.current_scope = ns_term;

        // Emit member facts for direct children
        self.emit_member_facts_for_items(&n.items, ns_term);

        // Load nested items within this namespace scope
        self.load_items(&n.items, Some(ns_term));

        self.current_scope = prev_scope;
    }

    /// True iff a `SortAlias(sort_term, _)` fact is already asserted. Reads pos 0
    /// carrier-agnostically (via `rule_head_value` / `pos_arg`) so a value-fact
    /// SortAlias head (a denoted target, e.g. `sort T = Vector[Int64, 3]`) dedups
    /// without panicking on the term-only `rule_head`. Shared by `load_abstract_sort`
    /// (`sort T = ?`) and `emit_type_param_backing_var` (WI-452 marked params): the
    /// pre-pass and `load_items` both reach a declaration, and a second SortAlias
    /// with a fresh target Var would leave the param backed by two divergent Vars.
    fn sort_alias_exists(&mut self, sort_term: TermId) -> bool {
        let alias_sym = self.kb.resolve_symbol("SortAlias");
        for rid in self.kb.rules_by_functor(alias_sym) {
            if !self.kb.is_fact(rid) {
                continue;
            }
            let head = self.kb.rule_head_value(rid);
            if head.pos_arg(self.kb, 0).and_then(|p| p.as_term_id()) == Some(sort_term) {
                return true;
            }
        }
        false
    }

    /// Assert a positional `SortAlias(sort_ref, target)` fact. Shared emission for
    /// `load_abstract_sort` and `emit_type_param_backing_var`.
    fn assert_sort_alias(
        &mut self,
        sort_term: TermId,
        target: crate::eval::value::Value,
        domain: TermId,
    ) {
        use crate::eval::value::Value;
        let alias_sym = self.kb.resolve_symbol("SortAlias");
        let sort_sort = self.kb.make_name_term("Sort");
        self.kb.assert_metadata_fact_carrier(
            alias_sym,
            vec![Value::term(sort_term), target],
            Vec::new(),
            sort_sort,
            domain,
            None,
        );
    }

    fn load_abstract_sort(&mut self, s: &AbstractSort, domain: TermId) {
        let sort_term = self.name_to_sort_term(&s.name);

        // Skip re-registration if this AbstractSort has already been loaded —
        // `load_sort_with_body`'s pre-pass calls us early so SortAlias is in place
        // before entity FieldInfo builds; the later `load_items` pass would
        // otherwise allocate a *second* SortAlias with a fresh target Var, leaving
        // each type-param backed by two distinct Vars (`find_sort_alias_var` then
        // returns the first by `rules_by_functor` order, which may differ from the
        // Var the entity field already captured).
        if self.sort_alias_exists(sort_term) {
            return;
        }

        self.kb.register_sort(sort_term, SortKind::Sort);

        // Both variable (sort T = ?Element) and alias (sort T = Int64) emit SortAlias.
        // For variables, use convert_term directly to avoid double-emitting descriptions
        // (AbstractSort.descriptions already covers them via the loop below).
        // WI-366: a denoted-bearing alias target (a value-in-type, e.g.
        // `sort T = Vector[Int64, 3]`) lowers to a `Value::Node` → the SortAlias
        // becomes a value fact carrying the occurrence; a ground target (the
        // universal case — a `Var` for `sort T = ?`, a `sort_ref` for `sort T = Int64`)
        // keeps the hash-consed `Term::Fn` head, byte-identical to the prior build.
        let target_value = match &s.definition {
            TypeExpr::Variable { term_id, .. } => {
                crate::eval::value::Value::term(self.convert_term(*term_id))
            }
            _ => self.type_expr_to_value(&s.definition),
        };
        // WI-390: lower a denoted-bearing alias target (value-in-type, e.g.
        // `sort T = Vector[Int64, 3]`) to a `TermId` so the SortAlias head stays a
        // hash-consed `Term::Fn`.
        let target_value = self.lower_value_or_gate(target_value, "sort alias", &s.definition);
        // SortAlias is positional: `SortAlias(sort_ref, target)`.
        self.assert_sort_alias(sort_term, target_value, domain);

        // Emit Description facts for all description blocks
        for desc_text in &s.descriptions {
            self.emit_desc_fact(sort_term, desc_text, domain);
        }
    }

    /// WI-452 (§5.4): emit `SortAlias(sort_term, Var)` — the non-rigid backing
    /// var that turns a MARKED structured sort param (`sort [F] { … }`, the HK
    /// carrier of `sort Spec[F[T]]`) into a type variable, mirroring
    /// `load_abstract_sort`'s `sort T = ?` path. `find_sort_alias_var` /
    /// `resolve_sort_alias` then return this `Var`, so F appears in
    /// `sort_type_params_as_pairs` and unifies/fills like any other type param.
    /// Emitted from `load_sort_with_body`'s pre-pass (before the entity FieldInfo
    /// build) so a reference to F resolves to this var, not a fresh divergent one.
    /// Dedup-guarded (shared `sort_alias_exists`) for a second load-order encounter.
    fn emit_type_param_backing_var(&mut self, sort_term: TermId, domain: TermId) {
        use crate::eval::value::Value;
        if self.sort_alias_exists(sort_term) {
            return;
        }
        let var_sym = self.kb.intern("_");
        let vid = self.kb.fresh_var(var_sym);
        let var_term = self.kb.alloc(Term::Var(Var::Global(vid)));
        self.assert_sort_alias(sort_term, Value::term(var_term), domain);
    }

    fn load_sort_with_body(&mut self, s: &SortWithBody, parent_domain: TermId) {
        let sort_term = self.name_to_sort_term(&s.name);
        self.defined_sorts.push(sort_term);
        let sort_sort = self.kb.make_name_term("Sort");

        let has_entities = s.items.iter().any(|item| matches!(item, Item::Entity(_)));
        let (sort_kind, kind_str) = match s.kind {
            SortDeclKind::Enum => (SortKind::Enum, "enum"),
            SortDeclKind::Sort => (SortKind::Sort, "sort"),
        };
        self.kb.register_sort(sort_term, sort_kind);

        // Emit Description facts for all description blocks
        for desc_text in &s.descriptions {
            self.emit_desc_fact(sort_term, desc_text, parent_domain);
        }

        // Set scope to sort for child resolution
        let prev_scope = self.current_scope;
        self.current_scope = sort_term;

        // Pre-load nested type-param SortAliases so they are in place before the
        // entity FieldInfo build calls `type_expr_to_value` on field types that
        // reference them. Without this, `entity foo(x: T)` runs before `sort T = ?`
        // in source order, hits `type_expr_to_child`'s fallback (no SortAlias yet),
        // and allocates a fresh `Var(name="T")` — a different Var than the
        // SortAlias's `Var(name="_")` registered later. The two Vars never unify, so
        // pattern substitution misses and the typer sees `head: Var(...)` where it
        // should see `head: String`. Both `load_abstract_sort` and
        // `emit_type_param_backing_var` dedupe on an already-asserted SortAlias, so
        // `load_items` below safely re-encounters these and no-ops. Pass `sort_term`
        // (the enclosing sort's own domain) so the SortAlias fact lives in the same
        // domain the second pass would have used.
        //
        // WI-452 (§5.4): a MARKED structured param (`sort [F] { … }`, the HK carrier
        // of `sort Spec[F[T]]`) needs its `SortAlias → Var` here too — same ordering
        // reason: a bare or applied `F` in a field/op resolved during the entity
        // build below must find F's canonical backing var, not a fresh divergent
        // one. (`load_items` later loads F's own body / members.)
        for item in &s.items {
            match item {
                Item::AbstractSort(abs) => self.load_abstract_sort(abs, sort_term),
                Item::SortWithBody(inner) if inner.is_type_param => {
                    let f_term = self.name_to_sort_term(&inner.name);
                    self.emit_type_param_backing_var(f_term, sort_term);
                }
                _ => {}
            }
        }

        // Register direct entity children (entity → parent sort) and emit each
        // one's `EntityInfo`/`FieldInfo` metadata fact. The sort-parent link is
        // `register_entity_of`; the fact itself is built by the shared
        // [`Self::emit_entity_info`] (WI-630 also emits it for namespace-level
        // entities, from `load_entity`). Field types are lowered once here (the
        // fact side; `load_entity` lowers again for the field-type registry — the
        // pre-existing sort-body double-lower, out of scope for WI-630).
        let ei_syms = self.entity_info_syms();
        for item in &s.items {
            if let Item::Entity(e) = item {
                let ctor_term = self.name_to_sort_term(&e.name);
                self.kb.register_entity_of(ctor_term, sort_term);
                let lowered: Vec<crate::eval::value::Value> =
                    e.fields.iter().map(|f| self.type_expr_to_value(&f.ty)).collect();
                self.emit_entity_info(e, ctor_term, &lowered, &ei_syms, parent_domain);
            }
        }

        // Emit member facts for direct children
        self.emit_member_facts_for_items(&s.items, sort_term);

        // WI-201: pre-scan this sort's `provides` / `fact` carrier bindings so the
        // bare-spec sugar can NARROW `Spec.Member` to a bound carrier (`fact
        // WorkItemStore[State = WIS]` ⟹ `WorkItemStore.State` ≡ WIS) regardless of
        // whether the binding appears before or after the using operation. Saved/
        // restored around the body load so a nested sort's bindings don't leak out.
        let sort_carrier_bindings = self.scan_sort_carrier_bindings(&s.items);
        let prev_sort_carrier_bindings =
            std::mem::replace(&mut self.current_sort_carrier_bindings, sort_carrier_bindings);

        // Load all items within this sort's domain scope
        self.load_items(&s.items, Some(sort_term));

        self.current_sort_carrier_bindings = prev_sort_carrier_bindings;

        // Now collect constructors, operations, parameters, requires from child items
        // (after loading, so all names are resolved in sort scope)
        let sort_functor = match self.kb.get_term(sort_term) {
            Term::Fn { functor, .. } => *functor,
            _ => self.kb.intern("_unknown"),
        };

        let mut ctor_refs = Vec::new();
        let mut op_refs = Vec::new();
        let mut param_refs = Vec::new();
        let mut req_terms = Vec::new();

        for item in &s.items {
            match item {
                Item::Entity(e) => {
                    let sym = self.remap_name(&e.name);
                    ctor_refs.push(self.kb.alloc(Term::Ref(sym)));
                }
                Item::Operation(o) => {
                    let sym = self.remap_name(&o.name);
                    op_refs.push(self.kb.alloc(Term::Ref(sym)));
                }
                Item::OperationBlock(ob) => {
                    for op in &ob.entries {
                        let sym = self.remap_name(&op.name);
                        op_refs.push(self.kb.alloc(Term::Ref(sym)));
                    }
                }
                Item::AbstractSort(abs) => {
                    if matches!(abs.definition, TypeExpr::Variable { .. }) {
                        let sym = self.remap_name(&abs.name);
                        param_refs.push(self.kb.alloc(Term::Ref(sym)));
                    }
                }
                Item::RequiresDecl(r) => {
                    // WI-366: `SortInfo.requires` is a reflection convenience (the
                    // faithful copy rides on the `SortRequiresInfo` value fact), so
                    // keep `SortInfo` a ground `Term` fact — a denoted-bearing spec
                    // (value-in-type binding) projects to its ground base sort here
                    // rather than forcing `SortInfo` (and its 9 term-only readers)
                    // to a value carrier.
                    let req_term = match self.sort_inst_to_value(&r.type_expr) {
                        crate::eval::value::Value::Term { id: t, .. } => t,
                        _ => match &r.type_expr {
                            TypeExpr::Simple(name) | TypeExpr::Parameterized { name, .. } => {
                                self.name_to_sort_term(name)
                            }
                            _ => self.kb.make_name_term("?"),
                        },
                    };
                    req_terms.push(req_term);
                }
                _ => {}
            }
        }

        self.emit_sort_info(sort_functor, has_entities, kind_str,
            &ctor_refs, &op_refs, &param_refs, &req_terms,
            sort_sort, parent_domain);

        // Auto-emit the induction principle for any sort with constructors,
        // including parameterised ones. The body uses positional fresh vars
        // (?head, ?tail, ...) in value position; it never references the
        // type parameter ?T, so polymorphism does not affect the rule
        // shape. (An earlier exclusion claimed cpp-gen would collide, but
        // cpp-gen iterates rules only via specific functor queries —
        // Implementation, SortInfo, OperationInfo, etc. — and never
        // enumerates `<Sort>.induction` rules.)
        if has_entities {
            self.emit_induction_rule(s, sort_term, sort_functor, parent_domain);
        }

        self.current_scope = prev_scope;
    }

    /// Emit `<Sort>.induction(?P) :- ho_apply(?P, ctor_1(...)), ...` —
    /// case analysis with one body goal per constructor. For ctors
    /// with recursive fields (a field whose type is the sort itself),
    /// the goal is wrapped in `forall_impl` carrying the inductive
    /// hypothesis: `(forall(?f1, ..., ?fN), ho_apply(?P, ?fr) -: ho_apply(?P, ctor(...)))`
    /// where `?fr` is each recursive-position binder. The IH form
    /// is consumed at proof time by the SLD nested-impl resolver
    /// (WI-108) and the Z3 induction tactic (WI-101).
    fn emit_induction_rule(
        &mut self,
        s: &SortWithBody,
        sort_term: TermId,
        sort_functor: Symbol,
        parent_domain: TermId,
    ) {
        let entities: Vec<&Entity> = s.items.iter()
            .filter_map(|i| if let Item::Entity(e) = i { Some(e) } else { None })
            .collect();
        if entities.is_empty() { return; }

        let p_sym = self.kb.intern("P");
        let p_var = self.kb.fresh_var(p_sym);
        let p_term = self.kb.alloc(Term::Var(Var::Global(p_var)));

        let sort_name = match self.kb.symbols.get(sort_functor) {
            SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            SymbolDef::Unresolved { name } => name.clone(),
        };
        let induction_name = format!("{sort_name}.induction");
        // Scope the `induction` short-name to the SORT (not parent_domain).
        // Top-level sorts otherwise all share `_global`, where the first
        // call registers `induction → Symbol(N)` and subsequent calls
        // reuse that without inserting their qualified name into
        // `by_qualified_name` — making each subsequent <Sort>.induction
        // unreachable by qualified-name lookup.
        let induction_sym = if let Some(&existing) = self.kb.symbols.by_qualified_name.get(&induction_name) {
            existing
        } else {
            self.kb.symbols.define(
                "induction", &induction_name, SymbolKind::Goal, sort_term.raw(),
            )
        };

        let head = self.kb.alloc(Term::Fn {
            functor: induction_sym,
            pos_args: SmallVec::from_slice(&[p_term]),
            named_args: SmallVec::new(),
        });

        // Use the resolved qualified-name symbol so the builtin tag
        // (BuiltinTag::HoApply registered against `anthill.reflect.Expr.ho_apply`)
        // recognises auto-generated induction rule bodies. Falling back
        // to bare intern would create an unresolved symbol disconnected
        // from the builtin tag.
        let ho_apply_sym = self.kb.symbols
            .by_qualified_name
            .get("anthill.reflect.Expr.ho_apply")
            .copied()
            .unwrap_or_else(|| self.kb.intern("ho_apply"));
        let tuple_sym = self.kb.intern("tuple");
        let forall_impl_sym = self.kb.intern("forall_impl");

        let mut body: Vec<TermId> = Vec::new();
        for e in entities {
            let ctor_sym = self.remap_name(&e.name);
            if e.fields.is_empty() {
                let ctor_term = self.kb.alloc(Term::Ref(ctor_sym));
                body.push(self.alloc_pos_fn(ho_apply_sym, &[p_term, ctor_term]));
                continue;
            }

            // Build binder vars per field, classifying recursive positions.
            let mut field_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            let mut binder_vars: SmallVec<[TermId; 4]> = SmallVec::new();
            let mut recursive_vars: SmallVec<[TermId; 2]> = SmallVec::new();
            for f in &e.fields {
                let f_name_str = self.parsed.symbols.name(f.name).to_owned();
                let f_sym = self.kb.intern(&f_name_str);
                let var = self.kb.fresh_var(f_sym);
                let var_term = self.kb.alloc(Term::Var(Var::Global(var)));
                field_args.push((f_sym, var_term));
                binder_vars.push(var_term);
                if self.field_is_recursive(&f.ty, sort_functor) {
                    recursive_vars.push(var_term);
                }
            }

            let ctor_term = self.kb.alloc(Term::Fn {
                functor: ctor_sym,
                pos_args: SmallVec::new(),
                named_args: field_args,
            });
            let consequent_goal = self.alloc_pos_fn(ho_apply_sym, &[p_term, ctor_term]);

            if recursive_vars.is_empty() {
                body.push(consequent_goal);
                continue;
            }

            // Inductive case: wrap in forall_impl(binders, ihs, [consequent]).
            let ihs: Vec<TermId> = recursive_vars.iter()
                .map(|&rv| self.alloc_pos_fn(ho_apply_sym, &[p_term, rv]))
                .collect();
            let binders_tuple = self.alloc_pos_fn(tuple_sym, &binder_vars);
            let ihs_tuple = self.alloc_pos_fn(tuple_sym, &ihs);
            let consequent_tuple = self.alloc_pos_fn(tuple_sym, &[consequent_goal]);
            body.push(self.alloc_pos_fn(
                forall_impl_sym,
                &[binders_tuple, ihs_tuple, consequent_tuple],
            ));
        }

        let rule_sort = self.kb.make_name_term("Rule");
        let body_nodes = self.kb.term_body_to_nodes(&body);
        self.kb.assert_rule_debruijn_with_nodes(head, body_nodes, rule_sort, parent_domain, None);
    }

    /// True if `ty` is a `Simple` type whose remapped symbol equals the
    /// containing sort. Parameterised self-references aren't reached here
    /// because parameterised sorts skip induction emission upstream.
    fn field_is_recursive(&mut self, ty: &TypeExpr, sort_functor: Symbol) -> bool {
        match ty {
            // Resolve WITHOUT `remap_name`'s error-pushing path: this is a
            // structural probe ("does the field type name the enclosing
            // sort?"), not the field type's authoritative lowering (that is
            // `type_expr_to_value`, which classifies projections). A name that
            // doesn't resolve here — e.g. a projection spelling `P.Key`, which
            // the type lowering classifies separately — is simply not the
            // recursive sort; pushing `UnresolvedName` from here duplicated
            // (WI-429: and falsely failed) the real lowering's diagnostics.
            TypeExpr::Simple(n) => {
                let lookup = if n.segments.len() == 1 {
                    self.parsed.symbols.name(n.segments[0]).to_owned()
                } else {
                    join_segments(&self.parsed.symbols, &n.segments)
                };
                match self.kb.symbols.resolve_in_scope(&lookup, self.current_scope.raw()) {
                    ResolveResult::Found(s) => s == sort_functor,
                    // Preserve remap_name's qualified-name fallback so a
                    // fully-qualified self-reference (`t: my.ns.Tree` inside
                    // `sort Tree`) still flags recursive.
                    ResolveResult::NotFound if n.segments.len() > 1 => self
                        .kb
                        .symbols
                        .by_qualified_name
                        .get(&lookup)
                        .is_some_and(|&s| s == sort_functor),
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// Allocate `Term::Fn { functor, pos_args, named_args: empty }`.
    fn alloc_pos_fn(&mut self, functor: Symbol, pos_args: &[TermId]) -> TermId {
        self.kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::from_slice(pos_args),
            named_args: SmallVec::new(),
        })
    }

    /// Emit a SortInfo fact with the given components.
    fn emit_sort_info(
        &mut self,
        sort_functor: Symbol,
        has_entities: bool,
        kind_str: &str,
        ctor_refs: &[TermId],
        op_refs: &[TermId],
        param_refs: &[TermId],
        req_terms: &[TermId],
        sort_sort: TermId,
        parent_domain: TermId,
    ) {
        let sort_info_sym = self.kb.resolve_symbol("anthill.reflect.SortInfo");
        let name_sym = self.kb.intern("name");
        let kind_field_sym = self.kb.intern("kind");
        let definition_sym = self.kb.intern("definition");
        let constructors_sym = self.kb.intern("constructors");
        let operations_sym = self.kb.intern("operations");
        let parameters_sym = self.kb.intern("parameters");
        let requires_sym = self.kb.intern("requires");

        let field_order = vec![
            name_sym, kind_field_sym, definition_sym, constructors_sym,
            operations_sym, parameters_sym, requires_sym,
        ];
        self.kb.register_entity_fields(sort_info_sym, field_order.clone());

        let name_ref = self.kb.alloc(Term::Ref(sort_functor));
        let kind_sym = self.kb.intern(kind_str);
        let kind_term = self.kb.alloc(Term::Ident(kind_sym));

        let definition_term = if has_entities {
            self.kb.make_name_term_from_sym(sort_functor)
        } else {
            let anon_sym = self.kb.intern("?");
            let vid = self.kb.fresh_var(anon_sym);
            self.kb.alloc(Term::Var(Var::Global(vid)))
        };

        let ctors_list = build_list(self.kb, ctor_refs);
        let ops_list = build_list(self.kb, op_refs);
        let params_list = build_list(self.kb, param_refs);
        let requires_list = build_list(self.kb, req_terms);

        // Sort by declared field-list order so rule-body partial-named-arg
        // queries (which use the same order via convert_term) unify against
        // these facts. Sorting by Symbol::index() looks canonical but isn't —
        // the field names get interned in arbitrary order, so the index
        // sort silently diverges from the convert_term-side sort.
        let mut si_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::from_slice(&[
            (constructors_sym, ctors_list),
            (definition_sym, definition_term),
            (kind_field_sym, kind_term),
            (name_sym, name_ref),
            (operations_sym, ops_list),
            (parameters_sym, params_list),
            (requires_sym, requires_list),
        ]);
        let order: HashMap<Symbol, usize> = field_order.iter().enumerate().map(|(i, &s)| (s, i)).collect();
        si_args.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
        let fact_term = self.kb.alloc(Term::Fn {
            functor: sort_info_sym,
            pos_args: SmallVec::new(),
            named_args: si_args,
        });
        self.kb.assert_metadata_fact(fact_term, sort_sort, parent_domain, None);
    }

    /// Build and assert the `EntityInfo` metadata fact (with a per-field
    /// `FieldInfo` list) for entity `e` whose constructor identity is
    /// `ctor_term`, under the reflect `Sort` meta-sort in `domain`.
    ///
    /// `lowered` is the field types already lowered by the caller (once) via
    /// `type_expr_to_value`, in `e.fields` order — the caller ALSO needs them
    /// (for `register_entity_field_types`), and re-lowering here would double-fire
    /// the non-idempotent `emit_desc_fact` (a duplicate `Description` fact per
    /// described field). `syms` is the reflect symbol bundle resolved once by the
    /// caller (avoids per-entity re-resolution across a sort's entity loop).
    ///
    /// Shared by two callers (WI-630): the sort-body path
    /// (`load_sort_with_body`, whose loop first links the entity to its parent
    /// sort via `register_entity_of`) and the namespace-level path
    /// (`load_entity`). A namespace-level entity has NO parent sort, so it gets no
    /// `register_entity_of` — and the `entity_of` typing rule is guarded with a
    /// trailing `is_entity_of(?x, ?sort)` (the KB-index builtin, sort-body only;
    /// typing.anthill) so its namespace scope is not bound as a bogus parent.
    ///
    /// WI-342 S4c: entity field types are carrier-agnostic, mirroring the WI-348
    /// op-param value-`FieldInfo`. A denoted-bearing field type (a value-in-type
    /// like `Vector[Int64, 3]`) is a `Value::Node` → a *value* `FieldInfo` entity
    /// carrying the occurrence; a ground field type stays a hash-consed
    /// `FieldInfo` term. When any field is `Node` the fields list (and the
    /// `EntityInfo` head) become a value fact, so the occurrence is CARRIED rather
    /// than re-grounded. No field type in the current corpus is denoted-bearing,
    /// so `lowered` is `Value::Term` for every field and this stays byte-identical
    /// to the prior build; the value-fact branch is the readiness for that flip.
    fn emit_entity_info(
        &mut self,
        e: &Entity,
        ctor_term: TermId,
        lowered: &[crate::eval::value::Value],
        syms: &EntityInfoSyms,
        domain: TermId,
    ) {
        use crate::eval::value::Value;
        // WI-511: a registered nullary constructor identity is the canonical
        // `Ref(c)`; a not-yet-registered one is `Fn{c}`. Loud on any other head
        // (a metadata fact must top a real constructor functor).
        let ctor_functor = match self.kb.head_functor(ctor_term) {
            Some(f) => f,
            None => unreachable!(
                "entity ctor_term must be Fn/Ref, got {:?}",
                self.kb.get_term(ctor_term)
            ),
        };
        let ctor_qualified = self.kb.qualified_name_of(ctor_functor).to_owned();
        debug_assert_eq!(
            e.fields.len(), lowered.len(),
            "emit_entity_info: lowered field types must match e.fields"
        );
        let field_values: Vec<Value> = e.fields
            .iter()
            .zip(lowered)
            .map(|(f, type_value)| {
                let field_name_str = self.parsed.symbols.name(f.name).to_owned();
                let field_qualified = format!("{}.{}", ctor_qualified, field_name_str);
                let field_sym = if let Some(&existing) = self.kb.symbols.by_qualified_name.get(&field_qualified) {
                    existing
                } else {
                    self.kb.symbols.define(&field_name_str, &field_qualified, SymbolKind::Field, ctor_term.raw())
                };
                let name_term = self.kb.alloc(Term::Ref(field_sym));
                match type_value {
                    Value::Node(_) => {
                        // Denoted-bearing field type → value FieldInfo entity.
                        let named: Vec<(Symbol, Value)> = vec![
                            (syms.name, Value::term(name_term)),
                            (syms.type_name, type_value.clone()),
                        ];
                        Value::Entity {
                            functor: syms.field_info,
                            pos: std::rc::Rc::from(Vec::new()),
                            named: std::rc::Rc::from(named),
                        }
                    }
                    Value::Term { id: type_term, .. } => {
                        // Ground field type → hash-consed FieldInfo term.
                        Value::term(self.kb.alloc(Term::Fn {
                            functor: syms.field_info,
                            pos_args: SmallVec::new(),
                            named_args: SmallVec::from_slice(&[
                                (syms.name, name_term),
                                (syms.type_name, *type_term),
                            ]),
                        }))
                    }
                    // `type_expr_to_value` yields only `Value::Term` /
                    // `Value::Node` (TypeChild has two variants).
                    other => unreachable!("a field type is Term or Node, got {other:?}"),
                }
            })
            .collect();
        let (fields_field, fields_all_ground) = value_or_ground_list(self.kb, field_values);

        // Assert EntityInfo fact (name stores sort term for entity_of
        // compatibility). A denoted-bearing field forces a `Value::Node`
        // somewhere in the head, which a hash-consed `Term` cannot hold →
        // value fact; an all-ground head stays a hash-consed `Term::Fn`
        // (dedup, structural sharing).
        if fields_all_ground {
            let fields_list = match fields_field {
                Value::Term { id: t, .. } => t,
                _ => unreachable!("fields_all_ground ⇒ fields list is Value::Term"),
            };
            let entity_info_fact = self.kb.alloc(Term::Fn {
                functor: syms.entity_info,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(syms.name, ctor_term), (syms.fields, fields_list)]),
            });
            self.kb.assert_metadata_fact(entity_info_fact, syms.sort_sort, domain, None);
        } else {
            let named: Vec<(Symbol, Value)> = vec![
                (syms.name, Value::term(ctor_term)),
                (syms.fields, fields_field),
            ];
            let head = Value::Entity {
                functor: syms.entity_info,
                pos: std::rc::Rc::from(Vec::<Value>::new()),
                named: std::rc::Rc::from(named),
            };
            self.kb.assert_metadata_fact_value(head, syms.sort_sort, domain, None);
        }
    }

    /// Resolve the reflect symbols used by [`Self::emit_entity_info`] once, and
    /// register the `EntityInfo` field schema. A caller holds this across a
    /// sort's entity loop (or one namespace-level entity) so the resolution and
    /// the constant `register_entity_fields` are not repeated per entity.
    fn entity_info_syms(&mut self) -> EntityInfoSyms {
        let field_info = self.kb.resolve_symbol("anthill.reflect.FieldInfo");
        let entity_info = self.kb.resolve_symbol("anthill.reflect.EntityInfo");
        let name = self.kb.intern("name");
        let type_name = self.kb.intern("type_name");
        let fields = self.kb.intern("fields");
        self.kb.register_entity_fields(entity_info, vec![name, fields]);
        let sort_sort = self.kb.make_name_term("Sort");
        EntityInfoSyms { field_info, entity_info, name, type_name, fields, sort_sort }
    }

    fn load_entity(&mut self, e: &Entity, domain: TermId) {
        let functor = self.remap_name(&e.name);

        // WI-342: lower each field type ONCE, carrier-agnostically — a value-in-
        // type field (`Vector[Int64, 3]` / `Modify[c]`-shaped / dependent) is carried
        // as `Value::Node`, a ground field type as `Value::Term`. Lowering once
        // avoids double-firing per-field side effects like `emit_desc_fact` (a
        // described type-var field type) — so `lowered` is reused below for BOTH
        // the field-type registry and (WI-630) the namespace-level `EntityInfo`
        // emission, rather than re-lowering in `emit_entity_info`.
        let lowered: Vec<crate::eval::value::Value> = e.fields
            .iter()
            .map(|f| self.type_expr_to_value(&f.ty))
            .collect();
        let field_types: Vec<(Symbol, crate::eval::value::Value)> = e.fields
            .iter()
            .zip(&lowered)
            .map(|(f, v)| (self.reintern(f.name), v.clone()))
            .collect();

        // Register entity field TYPES (the carrier-agnostic literal-typing
        // hints) under the resolved entity symbol. WI-499: field NAMES are now
        // registered earlier, in `scan_definitions` pass-1
        // (`register_entity_field_names_scan`), so the positional→named desugar
        // and partial-expansion are load-order-independent; only the type-aware
        // lowering stays here.
        //
        // WI-515: this registry (plus the `EntityInfo` fact) is the ONLY
        // declaration-side representation. The loader used to also assert a
        // same-functor "schema fact" (`edge(from: <Node type>, to: <Node type>)`
        // under sort `Entity`), but a fact whose DATA slots carry TYPE terms
        // unifies with any fully-var query over the constructor — e.g. the
        // self-referential constraint `no ?p -: edge(from: ?p, to: ?p)` matched
        // it (`?p = Node` in both slots) and was spuriously violated on
        // self-loop-free data, and every `KB.execute` pattern query saw a
        // phantom row. The reflect readers (`KB.fields`, `sort_query`) resolve
        // the entity BY REFERENCE (WI-632) and read this registry by functor.
        self.kb.register_entity_field_types(functor, field_types);

        // WI-630 (everything-is-facts gap): a sort-body entity's `EntityInfo`
        // fact is emitted by `load_sort_with_body`'s loop (which also links it to
        // its parent sort). A namespace-level entity — one whose enclosing scope
        // is a namespace or the global scope, NOT a sort body — was previously
        // recorded ONLY in the Rust-side `entity_field_types` registry, invisible
        // to anthill-level reflect queries. Emit its `EntityInfo` here (reusing
        // `lowered`) so `EntityInfo(name: <entity>)` and `KB.fields` see it too.
        // The `is_sort_scope` guard avoids a double emission for sort-body
        // entities (which reach `load_entity` too, but under a sort scope). A
        // namespace-level entity has no parent sort, so the `entity_of` typing
        // rule is guarded with a trailing `is_entity_of(?x, ?sort)` (the KB-index
        // builtin) to not bind the namespace scope as a bogus parent
        // (typing.anthill).
        if !is_sort_scope(&self.kb, self.current_scope) {
            let ei_syms = self.entity_info_syms();
            let ctor_term = self.name_to_sort_term(&e.name);
            self.emit_entity_info(e, ctor_term, &lowered, &ei_syms, domain);
        }
    }

    fn load_fact(&mut self, f: &Fact, domain: TermId) {
        let sort_name = f.sort.as_deref().unwrap_or("Fact");
        let fact_sort = self.kb.make_name_term(sort_name);

        // Set owner: use the fact's head functor symbol if available
        let prev_owner = self.current_owner;
        if let Term::Fn { functor, .. } = self.parsed.terms.get(f.term) {
            self.current_owner = Some(self.remap_symbol(*functor));
        }

        // WI-618: facts are rules with empty bodies — a keyword-less lambda
        // typo in a fact argument would otherwise assert inert arrow data.
        self.check_bare_arrow_typo(f.term, "a fact", &HashSet::new());

        // WI-716: a fact head is a ground VALUE — mark the conversion so the
        // partial-named-arg expansion defaults an absent OPTIONAL field to
        // `none()` rather than an unbound var (which would unsoundly unify a
        // `some(?)` pattern; see `convert_term_with_expected`).
        self.in_value_position = true;
        let term = self.convert_term(f.term);
        self.in_value_position = false;
        // Record the fact's top-level term span on the side-tables so
        // typing.rs error formatting can resolve it back to a span.
        self.create_occurrence(f.term, term);

        let meta = f.meta.as_ref().map(|mb| self.load_meta_block(mb));
        let rule_id = self.kb.assert_fact(term, fact_sort, domain, meta);
        self.fact_rule_ids.push(rule_id);

        // WI-210: when `fact Spec[bindings]` appears inside a sort body
        // and Spec is itself a parameterized sort, also emit a
        // SortProvidesInfo so dispatch (and proposal-030 specialization
        // witnesses) can find the impl. Mirrors load_provides_clause.
        // Brings the loader in line with kernel-language §1418.
        self.maybe_emit_fact_provides_info(term, domain);

        self.current_owner = prev_owner;
    }

    /// WI-449: canonicalize a FACT-derived spec binding VALUE to the canonical,
    /// `provides`-identical [`Value`](crate::eval::value::Value) — the fact-path
    /// counterpart of [`sort_inst_to_value`]'s recursive lowering. The parser builds
    /// a parameterized binding value POSITIONALLY (`fact Effect[T = Modify[?]]` → the
    /// `Modify[?]` value is `Fn{Modify, pos:[?], named:[]}`; a nested
    /// `fact IndexedSeq[List[T], T]` → the `List[T]` value is `Fn{List, pos:[T]}`),
    /// because parse has no `type_params_of_sort` to map positional args onto the
    /// base sort's declared params, and a positional-only `Fn` is MALFORMED for
    /// `type_head` (only `Fn{base, named}` is `Parameterized`; a no-named-arg `Fn`
    /// → `TypeExtractor::Error`). Re-lower it here — at the load-time producer of the
    /// `SortProvidesInfo` `SortView` — into the SAME `SortView(base, …named)` carrier
    /// `sort_inst_to_value` builds: positional args map onto the base sort's declared
    /// params, recursively. The result is byte-identical to the `provides` emission
    /// and is read by the SAME `unwrap_spec_view` / `provides_spec_base_sym` dispatch
    /// machinery (which reads named bindings only off a `SortView` wrapper, never off
    /// a bare `Fn`). A leaf (`Ref` / `Ident` / a literal) or a NON-sort `Fn` (a reflect
    /// constructor) is already a canonical `Value::Term` and passes through unchanged.
    ///
    /// Reachable for every parameterized fact binding, and lossless. The return is
    /// ALWAYS a `Value::Term`: a user `fact` head is built by `convert_term` and
    /// asserted via `assert_fact` (there is no value-fact head for user facts), so
    /// the `value` reaching here is a hash-consed `Term` — even a denoted place
    /// `Modify[c]` rides as `Ref(c)`, never a `Value::Node`. Every leaf is therefore
    /// a `Value::Term` and `assemble_sort_view_value` collapses to a hash-consed
    /// `SortView` term, preserving every argument (the positional→named remap is the
    /// only reshaping). `Value` is the return type purely to share
    /// `assemble_sort_view_value` with the `provides` path, whose `type_expr_to_value`
    /// CAN lower a denoted place to a real `Value::Node` (the only `Value::Entity`
    /// producer).
    fn canonicalize_fact_binding_value(&mut self, value: TermId) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        let (functor, pos_args, named_args) = match self.kb.get_term(value) {
            Term::Fn { functor, pos_args, named_args } => {
                (*functor, pos_args.clone(), named_args.clone())
            }
            _ => return Value::term(value),
        };
        // Only a parameterized SORT instantiation re-lowers to a `SortView`.
        if !matches!(self.kb.kind_of(functor), Some(SymbolKind::Sort)) {
            return Value::term(value);
        }
        let params = self.kb.type_params_of_sort(functor);
        // Recurse into any explicit named values, then map each positional arg onto
        // the base sort's declared param in order.
        let mut named: Vec<(Symbol, Value)> = named_args
            .iter()
            .map(|(s, v)| (*s, self.canonicalize_fact_binding_value(*v)))
            .collect();
        // A stray positional (double-bind, or more positionals than declared params)
        // is a malformed instantiation kept in `pos` — invisible to the SortView
        // Value::Entity branch's readers but preserved rather than dropped.
        let mut pos: Vec<Value> = Vec::new();
        let mut positional_index: usize = 0;
        for pos_val in pos_args.iter() {
            let cv = self.canonicalize_fact_binding_value(*pos_val);
            match params.get(positional_index) {
                Some(param_name) => {
                    positional_index += 1;
                    let param_sym = self.kb.intern(param_name);
                    if named.iter().any(|(s, _)| *s == param_sym) {
                        pos.push(cv);
                    } else {
                        named.push((param_sym, cv));
                    }
                }
                None => pos.push(cv),
            }
        }
        // WI-600: a nested parameterized sort application is the PLAIN `Fn{base,
        // named}`, NOT a `reflect.SortView` wrapper — the fact-path twin of
        // `sort_binding_to_value`, byte-identical so a `fact Spec[…]` and a
        // `provides Spec[…]` emit the same spec (WI-449). Only the OUTER spec view
        // (assembled by `maybe_emit_fact_provides_info` / `sort_inst_to_value` via
        // `assemble_sort_view_value`) is a `SortView`. A denoted-bearing child or a
        // stray positional (which a hash-consed `Fn` can't hold) falls back to the
        // faithful `SortView` `Value::Entity` carrier.
        self.assemble_binding_value(functor, named, pos)
    }

    /// WI-600 — assemble a NESTED parameterized binding VALUE (`Element = Pair[A =
    /// K, B = V]`), choosing the faithful representation: the PLAIN parameterized
    /// term `Fn{base, named}` when every binding is ground and no stray positional
    /// remains, else the `reflect.SortView` `Value::Entity` carrier (a denoted child
    /// — value-in-type — a stray/overflow positional, or a double-bind can't ride a
    /// hash-consed `Fn`; a `SortView` Entity carries them faithfully rather than
    /// silently dropping, per the repo's loud-over-silent rule). The single decision
    /// point shared by [`sort_binding_to_value`] (the `provides` path) and
    /// [`canonicalize_fact_binding_value`] (the `fact` path), so the two emit
    /// BYTE-IDENTICAL specs for every input (WI-449) — the plain `Fn` only replaces
    /// the former nested `SortView` for the clean, well-formed case, exactly where
    /// carrier grounding compares it against a user-written `Pair[…]` (also a plain
    /// `Fn`) with no SortView→Fn rebuild. `pos` holds only the stray positionals
    /// (overflow / double-bind); the base name term is prepended for the SortView
    /// subject slot, mirroring the outer spec view.
    fn assemble_binding_value(
        &mut self,
        base_sym: Symbol,
        named: Vec<(Symbol, crate::eval::value::Value)>,
        pos: Vec<crate::eval::value::Value>,
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        if pos.is_empty() && named.iter().all(|(_, v)| matches!(v, Value::Term { .. })) {
            let base_ref = self.kb.make_sort_ref(base_sym);
            let ground: Vec<(Symbol, TermId)> =
                named.iter().map(|(s, v)| (*s, v.expect_term())).collect();
            Value::term(self.kb.make_parameterized_type(base_ref, &ground))
        } else {
            let name_term = self.kb.make_name_term_from_sym(base_sym);
            let mut all_pos = vec![Value::term(name_term)];
            all_pos.extend(pos);
            self.assemble_sort_view_value(all_pos, named)
        }
    }

    /// If `fact_term` is `Spec[bindings]` claiming spec satisfaction,
    /// emit a `SortProvidesInfo(sort_ref=<carrier>, spec=SortView(Spec,
    /// <named bindings>))` alongside the bare fact. Two recognised
    /// shapes (kernel-language §1418 + the stdlib namespace-level
    /// convention):
    /// - **Sort-body**: `current_scope` is a sort. The carrier is
    ///   `current_scope` itself; bindings come from the fact.
    /// - **Namespace-level**: `current_scope` is a namespace.
    ///   The carrier is derived from the fact's first binding value
    ///   (the type that satisfies the spec).
    ///
    /// Positional bindings are translated to named bindings via
    /// `type_params_of_sort` — `fact Ring[Float]` and
    /// `fact Ring[T = Float]` produce equivalent `SortView` records.
    fn maybe_emit_fact_provides_info(&mut self, fact_term: TermId, domain: TermId) {
        // fact_term must be `Fn { functor, … }` where functor is a Sort
        // with at least one type parameter (i.e. a spec).
        let (fact_functor, fact_pos_args, fact_named_args) =
            match self.kb.get_term(fact_term) {
                Term::Fn { functor, pos_args, named_args } => {
                    (*functor, pos_args.clone(), named_args.clone())
                }
                // WI-365: a BARE provider fact (`fact Box`, no `[bindings]`) is a
                // name term, not a `Fn`. A spec parametric only in an EFFECT row
                // (`effects Effect = ?`) has no type-argument bindings to write —
                // effects aren't expressible as type arguments (WI-301) — so its
                // provider claim is necessarily bare. Treat it as a zero-binding
                // provider so a carrier (`MutBox`) is still found at dispatch.
                Term::Ref(functor) | Term::Ident(functor) => {
                    (*functor, SmallVec::new(), SmallVec::new())
                }
                _ => return,
            };
        if !matches!(self.kb.kind_of(fact_functor), Some(SymbolKind::Sort)) {
            return;
        }
        let spec_params = self.kb.type_params_of_sort(fact_functor);
        // WI-407: a NON-parametric spec (`spec_params` empty) still declares a
        // real is-a — `sort QueryableStore { fact Store }`, top-level `fact
        // BulkStore[IndexedFileStore]`. Pre-WI-407 the gate was
        // `spec_params.is_empty()`, so those edges never reached
        // `SortProvidesInfo` and the declared hierarchy was invisible to
        // subtyping (the gap WI-385's arg/field validation surfaced). Emit a
        // zero-binding provider edge for them too. BUT a non-parametric sort
        // that has CONSTRUCTORS is a data sort, not a spec: `sort Holder { fact
        // Color[..] }` with `entity red/green` on Color asserts a data instance,
        // not is-a (wi210 `fact_for_non_spec_sort_does_not_emit_provides_info`).
        // So skip only the constructor-shaped non-parametric case; a parametric
        // fact still emits exactly as before (the `&& spec_params.is_empty()`
        // keeps a parametric data sort like `List` on its old path).
        if spec_params.is_empty() && self.kb.sort_has_constructors(fact_functor) {
            return;
        }

        use crate::eval::value::Value;
        // Translate positional bindings → named, using the spec's declared
        // parameter order. type_params_of_sort returns short names; positional[i]
        // binds to params[i]. Empty for a non-parametric spec — the loop does
        // nothing and `named_terms` stays whatever the user wrote (typically
        // nothing). These are the ORIGINAL (parse-shape) term bindings; the carrier
        // is read off them (its base sort is unaffected by canonicalization).
        let mut named_terms: SmallVec<[(Symbol, TermId); 2]> = fact_named_args.clone();
        for (i, pos_val) in fact_pos_args.iter().enumerate() {
            let param_name = match spec_params.get(i) {
                Some(n) => n.clone(),
                None => continue,
            };
            let param_sym = self.kb.intern(&param_name);
            // Skip if user already supplied this name explicitly.
            if named_terms.iter().any(|(s, _)| *s == param_sym) {
                continue;
            }
            named_terms.push((param_sym, *pos_val));
        }

        // Determine sort_ref (the carrier). For sort-body facts, it's
        // the enclosing sort. For namespace-level facts, it's the
        // first binding value's underlying sort symbol.
        let domain_functor = match self.kb.get_term(domain) {
            Term::Fn { functor, .. } => *functor,
            _ => return,
        };
        let sort_ref_term = match self.kb.kind_of(domain_functor) {
            Some(SymbolKind::Sort) => domain,
            Some(SymbolKind::Namespace) => {
                // Derive the carrier from the spec's CARRIER ("Self") TYPE
                // PARAMETER — the first-declared TYPE binding — NOT
                // `named_terms.first()`. Two reasons the first binding is not
                // reliably the carrier: (1) a POSITIONAL binding is translated and
                // APPENDED after the named ones, so in `fact Combiner[Tag, combine
                // = tagCombine]` the leading binding is the OP `combine`; (2)
                // `fact_value_to_sort_sym` returns the symbol of a bare
                // `Ref`/`Ident` WITHOUT a Sort check, so an op binding would file
                // the provision under the operation `tagCombine` instead of `Tag`
                // (WI-431 (E)). Selecting the non-op binding with the lowest SYMBOL
                // INDEX (= earliest declared) finds the carrier regardless of
                // written order, skips op bindings, and works for a structured /
                // higher-kinded carrier param (`CpsMonad`'s `F`) that
                // `type_params_of_sort` does not list. WI-407: a NON-parametric
                // spec has no type param, so the raw leading positional IS the
                // carrier (`fact BulkStore[IndexedFileStore]` ⇒ `IndexedFileStore`).
                let carrier_val = named_terms
                    .iter()
                    .filter(|(_, v)| binding_op_symbol(self.kb, *v).is_none())
                    .min_by_key(|(s, _)| s.index())
                    .map(|(_, v)| *v)
                    .or_else(|| fact_pos_args.first().copied());
                // The carrier must be a TYPE (Sort or namespace-level Entity),
                // never an operation — a binding to an op value is a
                // mis-derivation, not a carrier.
                let carrier_sym = carrier_val
                    .and_then(|val| self.fact_value_to_sort_sym(val))
                    .filter(|s| !matches!(self.kb.kind_of(*s), Some(SymbolKind::Operation)));
                match carrier_sym {
                    Some(sym) => self.kb.make_name_term_from_sym(sym),
                    // WI-431 (E): a parametric INSTANCE FACT (binds ≥1 op) whose
                    // carrier cannot be derived is malformed — be LOUD instead of
                    // silently dropping the whole provision (and with it the
                    // coverage / coherence / signature checks). A type-only or bare
                    // provider fact (no op binding) keeps the lenient path: it may
                    // legitimately have no carrier here (a bare `fact BulkStore`).
                    None => {
                        // Loud only for a PARAMETRIC instance fact — `binds_any_op`
                        // AND a carrier type-param slot (`spec_params.first()`). A
                        // non-parametric spec has no carrier param to forget, and a
                        // type-only / bare provider fact (no op binding) keeps the
                        // lenient path.
                        let binds_any_op = named_terms
                            .iter()
                            .any(|(_, v)| binding_op_symbol(self.kb, *v).is_some());
                        if binds_any_op {
                            if let Some(carrier_param) = spec_params.first() {
                                self.errors.push(LoadError::UnresolvableInstanceCarrier {
                                    spec: self.kb.qualified_name_of(fact_functor).to_string(),
                                    carrier_param: carrier_param.clone(),
                                });
                            }
                        }
                        return;
                    }
                }
            }
            _ => return,
        };

        // WI-449: re-lower each binding VALUE to its faithful, `provides`-identical
        // `Value` (`canonicalize_fact_binding_value` maps positional→named and rides
        // a denoted binding as a `Value::Entity`), then assemble the spec the SAME
        // way `sort_inst_to_value` does — so the fact and `provides` emissions are
        // byte-identical and a denoted binding is never flattened to a `TermId`.
        let named_values: Vec<(Symbol, Value)> = named_terms
            .iter()
            .map(|(s, v)| (*s, self.canonicalize_fact_binding_value(*v)))
            .collect();
        let spec_name_term = self.kb.make_name_term_from_sym(fact_functor);
        let spec_value = self.assemble_sort_view_value(vec![Value::term(spec_name_term)], named_values);

        // Assert SortProvidesInfo(sort_ref, spec) through the Value carrier — the
        // SAME path `load_provides_clause` uses, so an all-ground spec rides as a
        // hash-consed `Term::Fn` and a denoted-bearing one as a `Value::Entity`
        // value fact (one carrier decision, in `assert_fact_carrier`).
        let provides_sym = self.kb.resolve_symbol("anthill.reflect.SortProvidesInfo");
        let sort_ref_arg = self.kb.intern("sort_ref");
        let spec_arg = self.kb.intern("spec");
        self.kb.register_entity_fields(provides_sym, vec![sort_ref_arg, spec_arg]);
        let provides_sort = self.kb.make_name_term("Requirement");
        self.kb.assert_fact_carrier(
            provides_sym,
            Vec::new(),
            vec![(sort_ref_arg, Value::term(sort_ref_term)), (spec_arg, spec_value)],
            provides_sort,
            domain,
            None,
        );
    }

    /// Extract the underlying nominal symbol from a fact-binding value
    /// term. Handles `Ref`, `Ident`, and `Fn` shapes — the forms
    /// `convert_term` produces for a plain type reference (a sort or a
    /// namespace-level entity). NOTE: a bare `Ref`/`Ident` is returned
    /// unfiltered (it may resolve to a non-type symbol such as an operation);
    /// the carrier-derivation caller excludes `Operation` kinds itself, since a
    /// type carrier may legitimately be an `Entity` (`IndexedFileStore`) as well
    /// as a `Sort`.
    fn fact_value_to_sort_sym(&self, value: TermId) -> Option<Symbol> {
        match self.kb.get_term(value) {
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            Term::Fn { functor, .. } => {
                if matches!(self.kb.kind_of(*functor), Some(SymbolKind::Sort)) {
                    Some(*functor)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// WI-582 — collect the type-variable INTRODUCER names declared on a rule
    /// head (`[T]` after the head functor, e.g. `keep[T](…)`). The `[T]` rides as a
    /// call `type_args` side-channel (convert.rs). Read ONLY the head functor's
    /// type-args — the LHS of an equational head `keep[T](…) = rhs` — NOT
    /// recursively, so a concrete type-arg in the RHS or a nested call
    /// (`= wrap[Box](…)`) is not mistaken for an introducer (which would trip the
    /// "unbounded type-var" check). Only a bare, unbound name (`[T]`, `param =
    /// None`) is an introducer; a concrete binding (`[A = Int64]`) is a type
    /// application. Read-only; runs before head conversion so the `typed_var` strip
    /// and the body-guard scan know which annotations name an introduced type-var.
    fn collect_rule_tvar_names(&self, head_parse_id: TermId, out: &mut std::collections::HashSet<String>) {
        // For an equational head `keep[T](…) = rhs` the introducer rides on the
        // LHS operand (`pos_args[0]`), so read the type-args there rather than off
        // the whole `eq(lhs, rhs)` node. WI-619: recognize the equational head by
        // its connective FUNCTOR (`eq`/`unify`/`struct_eq`, the pratt desugar of
        // `=`/`<=>`/`===`), NOT by `pos_args.len() == 2` — a plain 2-ary predicate
        // head (`same_ty[t](?x, ?y)`) also has two positional args, and reading
        // type-args off `pos_args[0]` (the first ARGUMENT `?x`, which has none)
        // there would silently drop the head's `[t]` introducer (1-ary and 3-ary
        // heads read off the head node and worked; exactly 2-ary misfired).
        let target = match self.parsed.terms.get(head_parse_id) {
            Term::Fn { functor, pos_args, .. }
                if pos_args.len() == 2 && self.is_parse_equation_functor(*functor) =>
            {
                pos_args[0]
            }
            _ => head_parse_id,
        };
        if let Some(bindings) = self.read_parse_call_type_args(target) {
            for b in &bindings {
                if b.param.is_none() {
                    if let crate::parse::ir::TypeExpr::Simple(n) = &b.bound {
                        if n.segments.len() == 1 {
                            out.insert(self.parsed.symbols.name(n.segments[0]).to_owned());
                        }
                    }
                }
            }
        }
    }

    /// WI-619 — is this PARSE-side functor an equation connective (`eq` / `unify`
    /// / `struct_eq`, the pratt desugar of `=` / `<=>` / `===`)? Used to recognize
    /// an equational rule head `lhs = rhs` at the parse layer — where the head's
    /// `[T]` introducer rides on the LHS operand, not the `eq(lhs, rhs)` node.
    /// Delegates to [`pratt::is_equation_functor`] (single source of truth with the
    /// infix table that mints these functors), mirroring the KB-side
    /// [`is_equational_head`] which classifies the resolved qualified name instead.
    fn is_parse_equation_functor(&self, functor: Symbol) -> bool {
        pratt::is_equation_functor(self.parsed.symbols.name(functor))
    }

    /// WI-582 — recognize a body guard `Spec[X]` where `X` is a head-introduced
    /// type-var, returning `(X-short-name, Spec-parse-functor)`. This is the
    /// `[T]`-form's bound source: `:- Spec[T]` gives `T`'s bound. The shape is the
    /// one `convert.rs`'s `convert_instantiation_term` builds for a parameterized
    /// term in goal position: `Fn{functor: Spec, pos_args: [Ref(X)], named: []}`.
    fn try_body_tvar_guard(
        &self,
        gtid: TermId,
        introducers: &std::collections::HashSet<String>,
    ) -> Option<(String, Symbol)> {
        if let Term::Fn { functor, pos_args, named_args } = self.parsed.terms.get(gtid) {
            if named_args.is_empty() && pos_args.len() == 1 {
                if let Term::Ref(x_sym) = self.parsed.terms.get(pos_args[0]) {
                    let x_name = self.parsed.symbols.name(*x_sym).to_owned();
                    if introducers.contains(&x_name) {
                        return Some((x_name, *functor));
                    }
                }
            }
        }
        None
    }

    fn load_rule(&mut self, r: &Rule, domain: TermId) {
        let rule_sort = self.kb.make_name_term("Rule");

        // WI-582: desugar the `[T]` type-variable-introducer form into the inline
        // form. Collect the head's introduced type-vars (`[T]`) and map each to
        // the bound its body guard `Spec[T]` gives it; the `typed_var` strip then
        // resolves `?x: T` to that bound, and the folded guard goals are dropped
        // from the body. The inline `?x: Spec` form needs none of this — the
        // introducer set is empty and `rule_tvar_bounds` stays empty.
        self.rule_tvar_bounds.clear();
        let mut folded_guard_ids: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut introducers: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        {
            for h in &r.heads {
                if let RuleHead::Term(tid) = h {
                    self.collect_rule_tvar_names(*tid, &mut introducers);
                }
            }
            if !introducers.is_empty() {
                if let Some(body) = r.body.as_ref() {
                    for &gtid in body {
                        if let Some((tvar, spec_sym)) =
                            self.try_body_tvar_guard(gtid, &introducers)
                        {
                            if self.rule_tvar_bounds.contains_key(&tvar) {
                                // A type-variable's bound must be declared once; a
                                // second `Spec[T]` guard would be silently lost
                                // (overwrite + drop). Reject loudly. Still fold it
                                // out of the body to avoid a confusing secondary
                                // "unresolved name T" error.
                                self.errors.push(LoadError::Other {
                                    message: format!(
                                        "WI-582: rule type-variable `{tvar}` is bounded by more \
                                         than one guard; declare its bound once (a compound bound \
                                         spanning several guards is not yet supported)"
                                    ),
                                });
                                folded_guard_ids.insert(gtid.raw());
                                continue;
                            }
                            let kb_sym = self.remap_symbol(spec_sym);
                            let bound = self.kb.make_sort_ref(kb_sym);
                            self.rule_tvar_bounds.insert(tvar, bound);
                            folded_guard_ids.insert(gtid.raw());
                        }
                    }
                }
                // An introduced type-var with no bounding guard would yield a
                // non-nominal bound that never fires — flag it loudly rather than
                // silently load a rule that can never apply.
                let unbounded: Vec<String> = introducers
                    .iter()
                    .filter(|tv| !self.rule_tvar_bounds.contains_key(*tv))
                    .cloned()
                    .collect();
                for tv in unbounded {
                    self.errors.push(LoadError::Other {
                        message: format!(
                            "WI-582: rule type-variable `{tv}` has no bounding guard \
                             (expected a `:- Spec[{tv}]` clause to bound it)"
                        ),
                    });
                }
            }
        }

        let prev_owner = self.current_owner;
        if let Some(ref label) = r.label {
            self.current_owner = Some(self.remap_name(label));
        }

        // WI-618: rule type-vars (`[t]` introducers) live in rule_tvar_bounds,
        // never the symbol table — exempt them from the bare-arrow leaf test
        // so `?y <=> (t -> t)` over a rule tvar loads. ALL introducers are
        // exempt, not just bounded ones: an unbounded `[t]` already gets the
        // accurate WI-582 "no bounding guard" diagnostic above, and a second,
        // wrong-advice lambda hint on the same name would only mislead.
        let arrow_bound: HashSet<String> = introducers;

        // Single pass: build positive heads, detect any `⊥` head.
        let mut positive_heads: Vec<TermId> = Vec::with_capacity(r.heads.len());
        // WI-582: per positive-head typed-pattern bounds (`?x: T`), parallel to
        // `positive_heads`. `convert_term`'s `typed_var` strip records them into
        // `self.rule_head_type_bounds` while `in_rule_head` is set; drained here
        // and installed on each head's RuleEntry below.
        let mut head_type_bounds: Vec<Vec<(VarId, TermId)>> = Vec::with_capacity(r.heads.len());
        let mut has_bottom = false;
        for h in &r.heads {
            match h {
                RuleHead::Term(tid) => {
                    // WI-618: a keyword-less lambda typo in a head argument
                    // would otherwise ride as an inert, never-matching pattern.
                    self.check_bare_arrow_typo(*tid, "a rule head", &arrow_bound);
                    self.rule_head_type_bounds.clear();
                    self.in_rule_head = true;
                    // WI-716: a rule head is a VALUE the rule DERIVES — an
                    // entity-constructor head with an omitted optional field must
                    // store `none()`, not a `forall v` var (the same soundness
                    // rule as a fact head; see the `wi716` refutation of the
                    // fact-only fix). A non-entity head has no field expansion, so
                    // this is a no-op for it.
                    self.in_value_position = true;
                    let head = self.convert_term(*tid);
                    self.in_value_position = false;
                    self.in_rule_head = false;
                    head_type_bounds.push(std::mem::take(&mut self.rule_head_type_bounds));
                    positive_heads.push(head);
                }
                RuleHead::Bottom => has_bottom = true,
            }
        }

        // ⊥ does not combine with positive heads.
        if has_bottom && r.heads.len() > 1 {
            self.errors.push(LoadError::Other {
                message: "denial heads (`⊥`) cannot be combined with positive heads in a multi-head rule".to_string(),
            });
            self.current_owner = prev_owner;
            return;
        }

        // WI-246: build the rule's native occurrence body — the sole body
        // representation now that the term body is dropped. Each atom is walked
        // from the parse IR straight to a `NodeOccurrence`
        // (`build_body_atom_occurrence`), which seeds `self.var_map` itself for
        // shared var identity across the body atoms and the (already-converted)
        // head, so `assert_rule_debruijn_with_nodes` can collect the rule's vars
        // from head + occurrences and close both to De Bruijn — no term body.
        let mut body_nodes: Vec<Rc<NodeOccurrence>> = Vec::new();
        if let Some(terms) = r.body.as_ref() {
            for &tid in terms {
                // WI-582: a folded `Spec[T]` guard — its content became the
                // bound on the `?x: T` variable, so it is not a body goal.
                if folded_guard_ids.contains(&tid.raw()) {
                    continue;
                }
                // WI-618: a keyword-less `pattern -> body` lambda typo in a
                // body goal would otherwise ride as inert arrow-term data.
                self.check_bare_arrow_typo(tid, "a rule body", &arrow_bound);
                body_nodes.push(self.build_body_atom_occurrence(tid));
            }
        }

        // WI-525 (proposal 049, Part A): a `<=>` (unify) under `not` must have
        // every variable bound by an earlier positive goal — else NAF on an
        // unbound unification is unsound.
        self.check_negated_unify_allowedness(&body_nodes);

        let meta = r.meta.as_ref().map(|mb| self.load_meta_block(mb));

        // Proposal 032: head IS the rule's claim. Labeled rules
        // remain citable through `RuleEntry.label` + `rules_by_label`.
        // Multi-head labeled rules (`rule X: H1, H2 :- B`) desugar
        // into N rules sharing label X, each with head H_i and the
        // same body B — `using X` fans out to all of them via
        // `rules_by_label[X]`.
        let label_sym = r.label.as_ref().map(|l| self.remap_name(l));

        let kb_heads: Vec<TermId> = match (&r.label, has_bottom, positive_heads.len()) {
            // Denial: head = ⊥. (Labeled cites via label index;
            // unlabeled denial is citable only by pattern.)
            (_, true, _) => vec![self.kb.alloc(Term::Bottom)],

            // Labeled — single or multi-head; each head becomes its
            // own rule sharing the label.
            (Some(_), false, _) => positive_heads,

            // Unlabeled single-head: head term IS the KB identity.
            (None, false, 1) => positive_heads,

            // Unlabeled multi-head: no unique citation handle.
            (None, false, _) => {
                self.errors.push(LoadError::Other {
                    message: "multi-head rule requires a label so the rule has a unique citation handle (e.g. `rule my_law: H1, H2 :- B`)".to_string(),
                });
                self.current_owner = prev_owner;
                return;
            }
        };

        for (head_idx, kb_head) in kb_heads.into_iter().enumerate() {
            let rid = self.kb.assert_rule_debruijn_with_nodes(
                kb_head, body_nodes.clone(), rule_sort, domain, meta);
            if let Some(label) = label_sym {
                self.kb.set_rule_label(rid, label);
            }
            // WI-582: install this head's typed-pattern bounds (if any) on the
            // RuleEntry, mapping each head variable to its DeBruijn index. A
            // denial (`⊥`) head has no positive-head bounds (index out of range
            // → `get` is None), so this is a no-op there. The bound is ENFORCED
            // only by the resolver's `apply_eq_rules` (a `[simp]`/`[unfold]`
            // directional rewrite over an equational head); on any other rule the
            // guard would be silently ignored, so reject it loudly rather than
            // load a rule whose `?x: T` does nothing (loud-over-silent).
            if let Some(bounds) = head_type_bounds.get(head_idx) {
                if !bounds.is_empty() {
                    let enforced = is_equational_head(self.kb, kb_head)
                        && (meta_has_flag(self.kb, meta, "simp")
                            || meta_has_flag(self.kb, meta, "unfold"));
                    if enforced {
                        self.kb.install_rule_type_bounds(rid, bounds);
                    } else {
                        self.errors.push(LoadError::Other {
                            message: "WI-582: typed rule patterns (`?x: T`) are supported only on \
                                      `[simp]`/`[unfold]` equational rewrite rules, where the \
                                      resolver enforces the bound; a non-rewrite rule would \
                                      silently ignore it. Tag the rule `[simp]`/`[unfold]` or \
                                      drop the annotation."
                                .to_string(),
                        });
                    }
                }
            }
            // WI-139: equational rules are cite-required by default.
            if is_equational_head(self.kb, kb_head)
                && !meta_has_flag(self.kb, meta, "simp")
                && !meta_has_flag(self.kb, meta, "unfold")
            {
                self.kb.unindex_functor(rid);
            }
        }

        self.current_owner = prev_owner;
    }

    /// WI-525 (proposal 049, NAF discipline — Part A): a `<=>` (unify) goal
    /// under `not(...)` binds, and negation-as-failure on a non-ground goal is
    /// unsound. Statically require that every variable in a negated unify is
    /// already bound by an EARLIER positive goal (strict left-to-right
    /// range-restriction, per the proposal; the looser order-independent form is
    /// a WI-526 revisit if a migrated rule false-positives). Operates on the
    /// BUILT occurrence body (resolved functors), classifying each atom with the
    /// same `get_builtin_view` the resolver uses, so `unify` / `not` are matched
    /// by their canonical `anthill.kernel.unify` / `anthill.reflect.not`
    /// symbols, not by parse-time spelling.
    fn check_negated_unify_allowedness(&mut self, body_nodes: &[Rc<NodeOccurrence>]) {
        let mut violations: Vec<(String, Span)> = Vec::new();
        // Var identity keyed by `VarId::raw()` (VarId is not `Hash`).
        let mut bound: HashSet<u32> = HashSet::new();
        for node in body_nodes {
            if self.kb.get_builtin_view(node) == Some(BuiltinTag::Not) {
                // A negated goal does NOT contribute bindings to the positive
                // store; instead, every unify nested under it is checked against
                // what the earlier positive goals have already bound.
                collect_negated_unify_violations(self.kb, node, &bound, &mut violations);
            } else {
                // A positive goal (including a positive `unify`, which binds)
                // range-restricts its variables.
                let mut vars = Vec::new();
                let mut seen = HashSet::new();
                node_occurrence::collect_occurrence_global_vars(node, &mut vars, &mut seen);
                for v in vars {
                    bound.insert(v.raw());
                }
            }
        }
        for (var_name, span) in violations {
            self.errors.push(LoadError::UnsafeNegatedUnify { var_name, span });
        }
    }

    /// WI-525 (proposal 049, NAF discipline — Part B): reject a BINDING `<=>` /
    /// `let` goal (both lower to `unify(?v, e)`) in a contract position. A
    /// contract must TEST, never bind. Classifies the goal's TOP-LEVEL functor:
    /// a `unify` under `not(...)` reads as `not` here and is left alone (it is a
    /// test via NAF). `parse_tid` is converted (memoized — the normal contract
    /// path converts the same term) so the functor resolves to its canonical
    /// `anthill.kernel.unify` before classification.
    fn reject_binding_unify_in_contract(&mut self, parse_tid: TermId, position: &str) {
        let goal = self.convert_term(parse_tid);
        if self.kb.get_builtin(goal) == Some(BuiltinTag::Unify) {
            self.errors.push(LoadError::BindingInContract {
                position: position.to_string(),
                span: self.parsed.terms.span(parse_tid),
            });
        }
    }

    /// WI-402 (existential half): detect `-> C ensures Spec[C, …]`. `C` is an
    /// op-discharged EXISTENTIAL carrier — the output dual of `requires Spec[C]`:
    /// the body witnesses it with a concrete provider, the caller sees the spec with
    /// the carrier abstract, and at eval the dictionary flows OUT with the value.
    ///
    /// The pattern: the return type is a single-segment Capitalized name that ALSO
    /// appears as the carrier (first positional) of an `ensures` spec, and is neither
    /// a declared op type-param (those are universal — caller-supplied) nor a
    /// resolvable sort (a CONCRETE return carrying an `ensures` postcondition is a
    /// different, valid case — never rewritten). Returns the carrier short name and the
    /// matching `ensures` spec atom (the raw parse `TermId`, for the return-type rewrite).
    fn detect_existential_carrier(&self, o: &Operation) -> Option<(String, TermId)> {
        let TypeExpr::Simple(ret_name) = &o.return_type else { return None };
        if ret_name.segments.len() != 1 {
            return None;
        }
        let ret_str = self.parsed.symbols.name(ret_name.segments[0]).to_owned();
        if !ret_str.chars().next().is_some_and(|c| c.is_uppercase()) {
            return None;
        }
        if o.type_params.iter().any(|tp| self.parsed.symbols.name(tp.name) == ret_str) {
            return None;
        }
        if !matches!(
            self.kb.symbols.resolve_in_scope(&ret_str, self.current_scope.raw()),
            ResolveResult::NotFound
        ) {
            return None;
        }
        let spec_atom = o
            .ensures
            .iter()
            .flatten()
            .copied()
            .find(|&atom| self.ensures_atom_carrier_name(atom).as_deref() == Some(ret_str.as_str()))?;
        Some((ret_str, spec_atom))
    }

    /// The carrier (first positional) short-name of an `ensures` spec atom
    /// (`KVStore[C, …]` ⟹ `Some("C")`), read from the RAW parse term.
    fn ensures_atom_carrier_name(&self, atom: TermId) -> Option<String> {
        let Term::Fn { pos_args, .. } = self.parsed.terms.get(atom) else { return None };
        self.parse_bare_name(*pos_args.first()?)
    }

    /// Short name of a bare-name parse term (the carrier-slot shapes: `Ident` / `Ref`
    /// / nullary `Fn`).
    fn parse_bare_name(&self, tid: TermId) -> Option<String> {
        match self.parsed.terms.get(tid) {
            Term::Ident(s) | Term::Ref(s) => Some(self.parsed.symbols.name(*s).to_owned()),
            Term::Fn { functor, pos_args, named_args }
                if pos_args.is_empty() && named_args.is_empty() =>
            {
                Some(self.parsed.symbols.name(*functor).to_owned())
            }
            _ => None,
        }
    }

    /// WI-402: register the existential carrier `C` as an op-scoped type variable and
    /// build the caller-visible return type = the `ensures` spec with the carrier
    /// dropped. The BOUND case (`ensures Spec[C, K = String]`) yields the manifest
    /// `Spec[K = String]` — reducing to the delivered manifest-return half; the
    /// UNBOUND case (`ensures Spec[C]`) yields a bare `Spec`, admitted by the
    /// ensures-aware `abstracting_return_error` gate. Registering `C` (symbol +
    /// type-param flag + `SortAlias` backing var, like `sort C = ?`) lets the
    /// `ensures` clause resolve the carrier and `sym_subject_key` treat it as a var.
    fn build_existential_return(
        &mut self,
        carrier: &str,
        spec_atom: TermId,
        op_qualified: &str,
        op_scope: TermId,
        domain: TermId,
    ) -> crate::eval::value::Value {
        let qualified = format!("{op_qualified}.{carrier}");
        let c_sym = self.kb.symbols.define(carrier, &qualified, SymbolKind::Sort, op_scope.raw());
        self.kb.symbols.add_type_param(op_scope.raw(), carrier);
        let c_sort_term = self.kb.alloc(Term::Fn {
            functor: c_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        self.emit_type_param_backing_var(c_sort_term, domain);

        let spec_term = self.convert_term(spec_atom);
        let return_term = self.strip_spec_carrier(spec_term, carrier);
        crate::eval::value::Value::term(return_term)
    }

    /// Drop the existential carrier from a converted spec application — the
    /// caller-visible spec type (`KVStore[C, K = String, V = String]` ⟹
    /// `KVStore[K = String, V = String]`; the unbound `KVStore[C]` ⟹ bare `KVStore`).
    /// Drops ONLY the carrier SLOT — the first positional argument (the carrier per
    /// `ensures_atom_carrier_name`). Named member bindings are kept verbatim, including
    /// one whose VALUE is the carrier (`V = C`, a member typed as the carrier): that is
    /// a legitimate member binding, not the carrier slot, and must survive.
    fn strip_spec_carrier(&mut self, spec_term: TermId, carrier: &str) -> TermId {
        let Term::Fn { functor, pos_args, named_args } =
            self.kb.get_term(spec_term).clone()
        else {
            return spec_term;
        };
        // Drop exactly the first positional whose leaf names the carrier; keep any
        // other positionals and ALL named bindings.
        let mut new_pos: SmallVec<[TermId; 4]> = SmallVec::new();
        let mut dropped_carrier = false;
        for a in pos_args {
            if !dropped_carrier && self.kb_leaf_name(a).as_deref() == Some(carrier) {
                dropped_carrier = true;
                continue;
            }
            new_pos.push(a);
        }
        let new_named = named_args;
        if new_pos.is_empty() && new_named.is_empty() {
            // Unbound existential (`ensures Spec[C]`) → the bare spec. Its canonical
            // form is `Ref(S)`, NOT a nullary `Fn{S}` — the latter `type_head`
            // classifies as `Error` (the WI-391 leaf shape), so a bare-spec return
            // would not be recognized as a provider upcast at the conformance check.
            return self.kb.alloc(Term::Ref(functor));
        }
        self.kb.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named })
    }

    /// Short name of a kb-term leaf (`Ref` / `Ident` / `Var` / nullary `Fn`), for
    /// carrier matching when stripping the existential carrier.
    fn kb_leaf_name(&self, tid: TermId) -> Option<String> {
        match self.kb.get_term(tid) {
            Term::Ref(s) | Term::Ident(s) => Some(self.kb.resolve_sym(*s).to_owned()),
            Term::Var(Var::Global(vid) | Var::Rigid(vid)) => {
                Some(self.kb.resolve_sym(vid.name()).to_owned())
            }
            Term::Fn { functor, pos_args, named_args }
                if pos_args.is_empty() && named_args.is_empty() =>
            {
                Some(self.kb.resolve_sym(*functor).to_owned())
            }
            _ => None,
        }
    }

    /// Proposal 039 / WI-084 — load a term-level constant. Records the declared
    /// type (carrier-agnostic `Value`, read fold-free by the typer) and, when
    /// present, converts and stores the defining-expression body. No folding, no
    /// value source, no purity gate yet — those are later phases; here a const is
    /// just a typed symbol with an optionally-stored body. The body resolves
    /// against the enclosing scope (a const has no params/result, so — unlike
    /// `load_operation` — it needs no dedicated op scope).
    fn load_const(&mut self, c: &Const, _domain: TermId) {
        let const_sym = self.remap_name(&c.name);

        // Own type/body occurrences by the const symbol (mirrors load_operation).
        let prev_owner = self.current_owner;
        self.current_owner = Some(const_sym);

        // Declared type — always present (grammar-mandatory); store it for the typer.
        let declared_type = self.type_expr_to_value(&c.ty);
        self.kb.set_const_type(const_sym, declared_type);

        // Defining body, if any (bodyless = host-supplied; value source is a later phase).
        if let Some(value_tid) = c.value {
            let (_handle, node) = self.convert_expr_term(value_tid);
            // WI-605: a body poisoned by a bare-arrow recovery Bottom is not
            // stored — the load is already failing with the targeted error.
            if !self.expr_body_bottom_recovery {
                self.kb.set_const_body_node(const_sym, node);
            }
        }

        self.current_owner = prev_owner;
    }

    fn load_operation(&mut self, o: &Operation, domain: TermId) {
        let op_sort = self.kb.make_name_term("Operation");
        let functor = self.remap_name(&o.name);

        // Set owner for expression occurrences
        let prev_owner = self.current_owner;
        self.current_owner = Some(functor);

        // Always enter the operation scope (scope created during scanning).
        // Even paramless operations have an op scope so that the reserved
        // `result` name is resolvable in effects / ensures positions
        // (proposal 041).
        let prev_scope = self.current_scope;
        let op_scope = self.kb.make_name_term_from_sym(functor);
        self.current_scope = op_scope;

        // WI-201: arm the bare-spec-member sugar for this operation's SIGNATURE. A bare
        // `Spec.Member` in a param / return / effect type position now mints a fresh op
        // type-param `?P` + a synthesized `requires Spec[Member = ?P]` (drained below,
        // before the requires / type_params lists are built). Restored after the
        // signature so it never leaks into the body or the next operation.
        let prev_bare_spec_sugar =
            std::mem::replace(&mut self.bare_spec_sugar, Some(BareSpecSugar::default()));

        // WI-489: a fresh place→type map for THIS signature (params + `result`),
        // populated below as each is converted and consulted by
        // `try_denoted_value_path` to validate value-in-type field projections.
        // Save/restore so it never leaks across operations.
        let prev_place_types = std::mem::take(&mut self.signature_place_types);

        let op_qualified = self.kb.qualified_name_of(functor).to_owned();

        // `result` as a parameter name collides with the reserved
        // return-value name; one diagnostic per operation suffices.
        if o.params.iter().any(|p| self.parsed.symbols.name(p.name) == "result") {
            self.errors.push(LoadError::Other {
                message: format!(
                    "operation '{}': parameter name 'result' is reserved for the return value; rename the parameter",
                    op_qualified
                ),
            });
        }

        // Pre-allocate type-param Vars and seed the per-scope cache so
        // later `type_expr_to_value` calls reuse them, and we can publish
        // the list on OperationInfo. Skipping the `find_sort_alias_var`
        // branch is intentional: an op type-param is its own logical
        // variable, distinct from any same-named outer SortAlias.
        let mut type_param_var_terms: Vec<TermId> = Vec::with_capacity(o.type_params.len());
        for tp in &o.type_params {
            let tp_name = self.parsed.symbols.name(tp.name).to_owned();
            let tp_sym = self.kb.intern(&tp_name);
            let cache_key = (op_scope.raw(), tp_name.clone());
            let var_tid = if let Some(&cached) = self.type_param_vars.get(&cache_key) {
                cached
            } else {
                let vid = self.kb.fresh_var(tp_sym);
                let tid = self.kb.alloc(Term::Var(Var::Global(vid)));
                self.type_param_vars.insert(cache_key, tid);
                tid
            };
            type_param_var_terms.push(var_tid);
        }

        // WI-341: the whole operation SIGNATURE flows through the Value path — a
        // denoted-bearing return type (an op returning a `Modify`-carrying
        // callback) is a `Value::Node`, never re-grounded via `type_expr_to_value`.
        // WI-402 (existential half): `-> C ensures Spec[C, …]` rewrites the return
        // type to the ensures spec with the carrier dropped (the body witnesses C
        // with a concrete provider; the caller sees the spec, carrier abstract).
        let return_value = match self.detect_existential_carrier(o) {
            Some((carrier, spec_atom)) => {
                // Record that THIS op's return was existential-rewritten, so the WI-401
                // abstracting-return gate admits its abstract return — and ONLY its.
                self.kb.existential_return_ops.insert(functor);
                self.build_existential_return(&carrier, spec_atom, op_qualified.as_str(), op_scope, domain)
            }
            None => self.type_expr_to_value(&o.return_type),
        };

        // WI-489: record the `result` binder's static type so a `Modify[result.a]`
        // projection in the effects clause (converted below) validates its field
        // path. An existential-rewritten return is recorded too — its abstract spec
        // shape simply causes the field walk to DEFER (not reject) when it cannot be
        // resolved concretely. Keyed by the SAME `result` symbol that
        // `try_denoted_value_path` resolves (`resolve_in_scope` from the op scope).
        if let ResolveResult::Found(result_sym) =
            self.kb.symbols.resolve_in_scope("result", op_scope.raw())
        {
            self.signature_place_types.insert(result_sym, return_value.clone());
        }

        // Build FieldInfo list for params
        let field_info_sym = self.kb.resolve_symbol("anthill.reflect.FieldInfo");
        let fi_name_sym = self.kb.intern("name");
        let fi_type_sym = self.kb.intern("type_name");
        // WI-341 Stage A: param types are carrier-agnostic. A callback param
        // whose arrow effect is denoted-bearing (`Modify[a]`) is a `Value::Node`
        // arrow → a *value* FieldInfo entity carrying the occurrence; a ground
        // param stays a hash-consed FieldInfo term. When any param is `Node` the
        // params list (and the OperationInfo head) become a value fact.
        let param_field_values: Vec<crate::eval::value::Value> = o.params
            .iter()
            .map(|p| {
                let param_name_str = self.parsed.symbols.name(p.name).to_owned();
                // Register field symbol for parameter
                let field_qualified = format!("{}.{}", op_qualified, param_name_str);
                let field_sym = if let Some(&existing) = self.kb.symbols.by_qualified_name.get(&field_qualified) {
                    existing
                } else {
                    self.kb.symbols.define(&param_name_str, &field_qualified, SymbolKind::Field, self.current_scope.raw())
                };
                let name_term = self.kb.alloc(Term::Ref(field_sym));
                // WI-341: bind a callback param's arrow param names to their
                // `CallbackParam` places for this arrow type's conversion, so a
                // self-referential effect (`Modify[a]`) resolves to `<op>.f.a`.
                // Cleared after so they never leak to the next param / the body.
                self.set_arrow_binder_scope(field_sym);
                let type_value = self.type_expr_to_value(&p.ty);
                self.arrow_binder_scope.clear();
                // WI-489: record this param's static type so a value-in-type field
                // projection off it (`Modify[c.backend]`) validates its field path in
                // the effects clause converted below. `field_sym` is the param's place
                // symbol (`<op>.<param>`) — the same one `try_denoted_value_path`
                // resolves for the head. Records incrementally, so a cross-parameter
                // projection (`b: a.head`) sees an earlier param's type.
                self.signature_place_types.insert(field_sym, type_value.clone());
                match type_value {
                    crate::eval::value::Value::Node(_) => {
                        // Denoted-bearing param type → value FieldInfo entity.
                        let named: Vec<(Symbol, crate::eval::value::Value)> = vec![
                            (fi_name_sym, crate::eval::value::Value::term(name_term)),
                            (fi_type_sym, type_value),
                        ];
                        crate::eval::value::Value::Entity {
                            functor: field_info_sym,
                            pos: std::rc::Rc::from(Vec::new()),
                            named: std::rc::Rc::from(named),
                        }
                    }
                    crate::eval::value::Value::Term { id: type_term, .. } => {
                        // Ground param type → hash-consed FieldInfo term.
                        crate::eval::value::Value::term(self.kb.alloc(Term::Fn {
                            functor: field_info_sym,
                            pos_args: SmallVec::new(),
                            named_args: SmallVec::from_slice(&[
                                (fi_name_sym, name_term),
                                (fi_type_sym, type_term),
                            ]),
                        }))
                    }
                    // `type_expr_to_value` yields only `Value::Term` / `Value::Node`
                    // (TypeChild has two variants), never `Value::Var`/entity.
                    other => unreachable!("a param type is Term or Node, got {other:?}"),
                }
            })
            .collect();
        let (params_field, params_all_ground) = value_or_ground_list(self.kb, param_field_values);

        // WI-348 (value-fact payoff): effect labels are carrier-agnostic
        // `Value`s and ride directly in the `OperationInfo` fact built below —
        // no `op_effects` side-table. A `Modify[c]` label is a `Value::Node` (a
        // `denoted` cannot be a hash-consed term); a ground label (`Error`) is a
        // `Value::Term`. When any label is non-`Term` the fact is built as a
        // *value fact* (Node-carrying head, `assert_fact_value`); when all are
        // `Term` it stays a hash-consed fact. Either way `lookup_operation_info`
        // reads these same labels back from the fact.
        let effect_values: Vec<crate::eval::value::Value> = o.effects
            .iter()
            .map(|e| self.type_expr_to_value(&e.type_expr))
            .collect();

        // Build requires and ensures lists. Auto-requires inference
        // (WI-320 / proposal 045 §6 Phase 0) extends the user-written
        // requires with one `EffectsRuntime[Effects = E_i]` per free row
        // variable in the effects clause — see `infer_effects_row_requires`
        // for the row-variable heuristic and the spec examples.
        let auto_requires_terms = self.infer_effects_row_requires(o);
        // WI-201: disarm + drain the bare-spec sugar (the whole signature — return,
        // params, effects — has now been converted). Each minted carrier becomes an
        // extra op type-param AND a synthesized `requires Spec[Member = ?P]` clause
        // (rebuilt from the entry — `minted` is the single source), extending the
        // requires extra-terms alongside the WI-320 auto-requires. The candidate filter
        // `requires_entry_lends_member` accepts it: the spec DECLARES `member` and the
        // application MENTIONS `?P`, so it licenses dispatch and constrains `?P`.
        let sugar = std::mem::replace(&mut self.bare_spec_sugar, prev_bare_spec_sugar)
            .unwrap_or_default();
        let mut extra_requires = auto_requires_terms;
        for ((spec, member), var) in &sugar.minted {
            type_param_var_terms.push(*var);
            extra_requires.push(self.kb.alloc(Term::Fn {
                functor: *spec,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(*member, *var)]),
            }));
        }
        let requires_list = self.convert_clause_list_with_extra(&o.requires, &extra_requires);
        let ensures_list = self.convert_clause_list(&o.ensures);

        // WI-525 (proposal 049, Part B): a contract TESTS, it never binds — so a
        // binding `<=>` / `let` (a `unify` goal) in a `requires` / `ensures`
        // clause is rejected. Only the user-written clauses are checked; the
        // synthesized auto-requires / bare-spec extras are spec applications,
        // never unify.
        let no_tvars = HashSet::new();
        for clause in &o.requires {
            for &tid in clause {
                self.reject_binding_unify_in_contract(tid, "requires");
                // WI-618: a keyword-less lambda typo in a contract clause.
                self.check_bare_arrow_typo(tid, "a `requires` clause", &no_tvars);
            }
        }
        for clause in &o.ensures {
            for &tid in clause {
                self.reject_binding_unify_in_contract(tid, "ensures");
                self.check_bare_arrow_typo(tid, "an `ensures` clause", &no_tvars);
            }
        }

        // Convert expression body if present. WI-305: discard the term handle;
        // the occurrence is the sole stored body (op_body_node side-table). The
        // handle is no longer kept in any fact field (OperationInfo/OperationImpl
        // body fields dropped). The term is still built transiently inside
        // `convert_expr_term` because the native node-build reads it.
        let has_body = match o.body {
            Some(body_tid) => {
                let (_handle, node) = self.convert_expr_term(body_tid);
                // WI-605: a body poisoned by a bare-arrow recovery Bottom is
                // not stored — the load is already failing with the targeted
                // error, and the typer would loudly reject the Bottom leaf as
                // a post-elaboration form (a second, misleading error).
                // `has_body` stays true: the source does have a body.
                if !self.expr_body_bottom_recovery {
                    self.kb.set_op_body_node(functor, node);
                }
                true
            }
            None => false,
        };
        // WI-605: capture before any later convert_expr_term call could reset it;
        // gates the OperationImpl fact and the eq-rewrite equation below, which
        // would otherwise re-lower the poisoned body via convert_term (a path the
        // bare-arrow arm does not cover) into a live SLD rewrite rule carrying
        // the mis-parsed arrow term.
        let body_poisoned = self.expr_body_bottom_recovery;

        // WI-087: operation attributes. Lower the operation's `meta_block`
        // (`[Marker, Key: value, ...]`) into a `meta(key: value, ...)` term —
        // the same shape and reader idiom (`meta_has_flag` / `meta_value`) as
        // rule/fact meta. An absent meta_block yields an empty `meta()`, so the
        // OperationInfo `meta` field is always present. Built while still in the
        // operation scope so a term-valued attribute resolves against op names.
        let meta_term = match &o.meta {
            Some(mb) => self.load_meta_block(mb),
            None => {
                let meta_functor = self.kb.resolve_symbol("meta");
                self.kb.alloc(Term::Fn {
                    functor: meta_functor,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::new(),
                })
            }
        };

        self.current_scope = prev_scope;
        self.current_owner = prev_owner;
        // WI-489: drop this signature's place→type map (restoring any enclosing one).
        self.signature_place_types = prev_place_types;

        // Build OperationInfo term with named args matching the entity definition
        let op_info_sym = self.kb.resolve_symbol("anthill.reflect.OperationInfo");
        let name_sym = self.kb.intern("name");
        let params_sym = self.kb.intern("params");
        let return_type_sym = self.kb.intern("return_type");
        let effects_sym = self.kb.intern("effects");
        let requires_sym = self.kb.intern("requires");
        let ensures_sym = self.kb.intern("ensures");
        let type_params_sym = self.kb.intern("type_params");
        let meta_sym = self.kb.intern("meta");

        // name: Ref to operation symbol
        let name_ref = self.kb.alloc(Term::Ref(functor));
        let type_params_list = build_list(self.kb, &type_param_var_terms);

        // WI-348: assemble the OperationInfo named args ONCE, carrier-agnostically.
        // Only `effects` varies by carrier: when every label is a ground
        // `Value::Term` the effects fit a hash-consed `TermId` cons-list and the
        // whole head stays a hash-consed term (the universal, dedup-able case);
        // when any label is a `Value::Node` (a `denoted` like `Modify[c]`) the
        // effects ride as a value cons-list and the head must be a value fact.
        // Every other field is always a ground `Value::Term`.
        use crate::eval::value::Value;
        let (effects_field, effects_all_ground) = value_or_ground_list(self.kb, effect_values);
        // WI-341: the head is a value fact when ANY of params / return / effects
        // carries a `Value::Node` (denoted-bearing); else a hash-consed `Term::Fn`.
        let all_ground =
            params_all_ground && effects_all_ground && matches!(return_value, Value::Term { .. });
        // Single source of truth for the field set / order. Readers resolve by
        // key (functor + `NamedKey(sym)`), so order is not load-bearing.
        let named: Vec<(Symbol, Value)> = vec![
            (name_sym, Value::term(name_ref)),
            (params_sym, params_field),
            (return_type_sym, return_value),
            (effects_sym, effects_field),
            (requires_sym, Value::term(requires_list)),
            (ensures_sym, Value::term(ensures_list)),
            (type_params_sym, Value::term(type_params_list)),
            // WI-087: operation attributes — always a ground `meta(...)` term, so
            // it never forces the value-fact path (does not enter `all_ground`).
            (meta_sym, Value::term(meta_term)),
        ];
        if all_ground {
            // Ground head → hash-consed `Term::Fn` (dedup, structural sharing).
            // Every field is a `Value::Term` here, so the extraction is total.
            let named_args: SmallVec<[(Symbol, TermId); 2]> = named
                .iter()
                .map(|(s, v)| match v {
                    Value::Term { id: t, .. } => (*s, *t),
                    _ => unreachable!("all_ground ⇒ every OperationInfo field is Value::Term"),
                })
                .collect();
            let op_info = self.kb.alloc(Term::Fn {
                functor: op_info_sym,
                pos_args: SmallVec::new(),
                named_args,
            });
            self.kb.assert_metadata_fact(op_info, op_sort, domain, None);
        } else {
            // A `denoted`-bearing effect forces a `Value::Node` somewhere in the
            // head, which a hash-consed `Term` cannot hold → value fact.
            let head = Value::Entity {
                functor: op_info_sym,
                pos: std::rc::Rc::from(Vec::<Value>::new()),
                named: std::rc::Rc::from(named),
            };
            self.kb.assert_metadata_fact_value(head, op_sort, domain, None);
        }

        // Emit OperationImpl fact for operations with expression bodies. WI-305:
        // the body field is dropped — the occurrence lives in op_body_node and is
        // reached via anthill.reflect.operation_body. WI-605: a poisoned body was
        // NOT stored, so don't claim an impl exists for it.
        if has_body && !body_poisoned {
            if let Some(op_impl_sym) = self.kb.try_resolve_symbol("anthill.realization.OperationImpl") {
                let impl_sort = self.kb.make_name_term("OperationImpl");
                let operation_key = self.kb.intern("operation");
                let params_key = self.kb.intern("params");

                let op_name_ref = self.kb.alloc(Term::Ref(functor));
                let param_syms: Vec<TermId> = o.params.iter().map(|p| {
                    let name = self.parsed.symbols.name(p.name).to_owned();
                    let sym = self.kb.intern(&name);
                    self.kb.alloc(Term::Ref(sym))
                }).collect();
                let params_list_impl = build_list(self.kb, &param_syms);

                let op_impl = self.kb.alloc(Term::Fn {
                    functor: op_impl_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (operation_key, op_name_ref),
                        (params_key, params_list_impl),
                    ]),
                });
                self.kb.assert_metadata_fact(op_impl, impl_sort, domain, None);
            }
        }

        // WI-605: skip the equation for a poisoned body — emit_operation_equation
        // re-lowers the body via `convert_term` (which the bare-arrow arm does not
        // cover), and the resulting `eq(op(...), <garbage arrow term>)` would be a
        // live SLD rewrite rule consulted by the still-running post-load passes
        // (constraint guards, provider-operation coverage).
        if !body_poisoned {
            if let Some(body_parse_id) = o.body {
                self.emit_operation_equation(o, functor, body_parse_id, domain);
            }
        }
    }

    /// Build `eq(<op>(?p1, ?p2, ...), body[params -> ?p_i])` and
    /// assert it as a rule with empty body, so SLD can apply operation
    /// definitions as rewrite rules during proof search.
    fn emit_operation_equation(
        &mut self,
        o: &Operation,
        op_functor: Symbol,
        body_parse_id: TermId,
        domain: TermId,
    ) {
        let body_kb = self.convert_term(body_parse_id);

        let mut param_vars: Vec<(Symbol, VarId)> = Vec::new();
        for p in &o.params {
            let pname = self.parsed.symbols.name(p.name).to_owned();
            let kb_sym = self.kb.intern(&pname);
            let var = self.kb.fresh_var(kb_sym);
            param_vars.push((kb_sym, var));
        }

        let body_with_vars = self.rewrite_param_refs(body_kb, &param_vars);

        let call_pos: SmallVec<[TermId; 4]> = param_vars.iter()
            .map(|(_, vid)| self.kb.alloc(Term::Var(Var::Global(*vid))))
            .collect();
        let call = self.kb.alloc(Term::Fn {
            functor: op_functor,
            pos_args: call_pos,
            named_args: SmallVec::new(),
        });

        // WI-644: head this operation-definition equation with the CANONICAL equation
        // functor (`eq_functor` = `anthill.prelude.PartialEq.eq` since the ops moved off
        // `Eq`), so SLD / `[simp]` (`rules_by_functor(eq_functor())`) find it — a bare
        // `intern("eq")` would head a symbol nothing looks up (WI-283).
        let eq_sym = self.kb.eq_functor();
        let head = self.kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[call, body_with_vars]),
            named_args: SmallVec::new(),
        });

        let eq_sort = self.kb.make_name_term("anthill.prelude.PartialEq");
        self.kb.assert_rule_debruijn_with_nodes(head, vec![], eq_sort, domain, None);
    }

    /// Replace `Ident(s)`/`Ref(s)` matching a parameter symbol with the
    /// corresponding `Var::Global`. Doesn't alpha-rename inside lambda
    /// or let bodies — shadowing param names is unsupported.
    fn rewrite_param_refs(&mut self, term: TermId, param_vars: &[(Symbol, VarId)]) -> TermId {
        match self.kb.get_term(term).clone() {
            Term::Ident(s) | Term::Ref(s) => {
                if let Some((_, vid)) = param_vars.iter().find(|(p, _)| *p == s) {
                    self.kb.alloc(Term::Var(Var::Global(*vid)))
                } else {
                    term
                }
            }
            Term::Fn { functor, pos_args, named_args } => {
                let mut new_pos: SmallVec<[TermId; 4]> = SmallVec::new();
                for &t in pos_args.iter() {
                    new_pos.push(self.rewrite_param_refs(t, param_vars));
                }
                let mut new_named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for &(n, t) in named_args.iter() {
                    new_named.push((n, self.rewrite_param_refs(t, param_vars)));
                }
                self.kb.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named })
            }
            _ => term,
        }
    }

    fn load_constraint(&mut self, c: &Constraint, domain: TermId) {
        let label = c.label.as_ref().map(|n| join_segments(&self.parsed.symbols, &n.segments));

        // WI-525 (proposal 049, Part B): a `constraint` body is a contract — it
        // TESTS, never binds. Reject any binding `<=>` / `let` (a `unify` goal)
        // anywhere in it, across all constraint forms.
        let mut constraint_goals: Vec<TermId> = Vec::new();
        collect_constraint_body_goal_tids(&c.body, &mut constraint_goals);
        let no_tvars = HashSet::new();
        for tid in constraint_goals {
            self.reject_binding_unify_in_contract(tid, "constraint");
            // WI-618: a keyword-less lambda typo in a constraint goal.
            self.check_bare_arrow_typo(tid, "a constraint", &no_tvars);
        }

        match &c.body {
            ConstraintBody::Denial { head, guard } => {
                // Historical behavior: store an inert `Constraint(head:, guard:)`
                // fact. Denial/invariant constraints are NOT registered as guards
                // (WI-023 wires only the quantified forms; enforcing the existing
                // denial constraints is a separate concern with its own regression
                // surface — the stdlib relies on them being inert today).
                self.store_denial_constraint_fact(head, guard.as_deref(), domain);
            }
            ConstraintBody::Quantified { .. } | ConstraintBody::Patterns(_) => {
                // WI-023: the guard EVALUATOR lowers a quantifier body as a pattern
                // conjunction and negates `forall` bodies per-goal. A `forall` whose
                // `-:` body is not a single pattern, or any quantifier with a NESTED
                // quantified/aggregation body, would mis-evaluate — reject loudly
                // rather than register a silently-wrong guard.
                if let Some(detail) = unsupported_quantifier_form(&c.body) {
                    self.errors.push(LoadError::UnsupportedConstraintForm {
                        label,
                        detail,
                        span: c.span,
                    });
                    return;
                }
                // WI-023: lower to a `LogicalQuery` guard and register it. The guard
                // is built as a hash-consed `TermId` (a stored structural reflect
                // value, legitimately hash-consable) and handed to the carrier-
                // agnostic `add_guard` via its `TermView` door.
                if let Some(lq) = self.build_logical_query(&c.body) {
                    self.kb.add_guard_labeled(lq, label);
                    self.store_logical_query_constraint_fact(lq, domain);
                }
            }
            ConstraintBody::Aggregation { .. } => {
                // WI-023 decision: parsed + carried faithfully, but the guard engine
                // cannot yet evaluate aggregation — a loud "not enforced" error
                // rather than a silently-vacuous guard.
                self.errors.push(LoadError::AggregationConstraintUnsupported {
                    label,
                    span: c.span,
                });
            }
        }
    }

    /// Store the inert `Constraint(head(…) [, guard(…)])` reflection fact for a
    /// denial/invariant constraint (the pre-WI-023 representation, unchanged).
    fn store_denial_constraint_fact(
        &mut self,
        head: &[TermId],
        guard: Option<&[TermId]>,
        domain: TermId,
    ) {
        let constraint_sort = self.kb.make_name_term("Constraint");
        let constraint_sym = self.kb.resolve_symbol("Constraint");

        let head_pos: SmallVec<[TermId; 4]> = head.iter().map(|&tid| self.convert_term(tid)).collect();
        let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
        let head_sym = self.kb.intern("head");
        let head_term = self.kb.alloc(Term::Fn {
            functor: head_sym,
            pos_args: head_pos,
            named_args: SmallVec::new(),
        });
        pos_args.push(head_term);

        if let Some(guard) = guard {
            let guard_pos: SmallVec<[TermId; 4]> = guard.iter().map(|&tid| self.convert_term(tid)).collect();
            let guard_sym = self.kb.intern("guard");
            let guard_term = self.kb.alloc(Term::Fn {
                functor: guard_sym,
                pos_args: guard_pos,
                named_args: SmallVec::new(),
            });
            pos_args.push(guard_term);
        }

        let constraint_term = self.kb.alloc(Term::Fn {
            functor: constraint_sym,
            pos_args,
            named_args: SmallVec::new(),
        });
        self.kb.assert_fact(constraint_term, constraint_sort, domain, None);
    }

    /// Store a queryable `Constraint(guard(<LogicalQuery>))` reflection fact for a
    /// guard-registered (quantified) constraint, for parity with the denial form.
    fn store_logical_query_constraint_fact(&mut self, lq: TermId, domain: TermId) {
        let constraint_sort = self.kb.make_name_term("Constraint");
        let constraint_sym = self.kb.resolve_symbol("Constraint");
        let guard_sym = self.kb.intern("guard");
        let guard_term = self.kb.alloc(Term::Fn {
            functor: guard_sym,
            pos_args: SmallVec::from_elem(lq, 1),
            named_args: SmallVec::new(),
        });
        let constraint_term = self.kb.alloc(Term::Fn {
            functor: constraint_sym,
            pos_args: SmallVec::from_elem(guard_term, 1),
            named_args: SmallVec::new(),
        });
        self.kb.assert_fact(constraint_term, constraint_sort, domain, None);
    }

    /// Resolve a `LogicalQuery` constructor symbol (`pattern_query`, `conjunction`,
    /// `forall_q`, …). `None` (with a loud load error) if `anthill.reflect` is not
    /// loaded, since a quantified constraint cannot then be lowered.
    fn logical_query_ctor(&mut self, short: &str) -> Option<Symbol> {
        let qn = format!("anthill.reflect.LogicalQuery.{short}");
        let sym = self.kb.try_resolve_symbol(&qn);
        if sym.is_none() {
            self.errors.push(LoadError::Other {
                message: format!("cannot lower quantified constraint: `{qn}` is unavailable (is anthill.reflect loaded?)"),
            });
        }
        sym
    }

    /// WI-023: build the `LogicalQuery` guard term for a quantified/leaf body.
    /// Returns `None` (with a load error already pushed) if a needed reflect
    /// constructor is unavailable.
    fn build_logical_query(&mut self, body: &ConstraintBody) -> Option<TermId> {
        match body {
            ConstraintBody::Quantified { quantifier, var, condition, body } => {
                let ctor = self.logical_query_ctor(quantifier.logical_query_functor())?;
                let cond_lq = self.build_patterns_lq(condition)?;
                let body_lq = self.build_logical_query(body)?;
                // The `var` slot carries the binder name (the engine identifies the
                // variable structurally, not by this name).
                let var_term = self.kb.alloc(Term::Const(Literal::String(var.clone())));
                let var_sym = self.kb.intern("var");
                let cond_sym = self.kb.intern("condition");
                let body_sym = self.kb.intern("body");
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::from_slice(&[
                    (var_sym, var_term),
                    (cond_sym, cond_lq),
                    (body_sym, body_lq),
                ]);
                // Canonical named-arg order (matches every other term builder /
                // the discrim index), so the reflect `Constraint(guard(…))` fact
                // hash-conses and unifies with a sorted-order LogicalQuery term.
                self.kb.canonicalize_record_named_args(ctor, &mut named_args);
                Some(self.kb.alloc(Term::Fn { functor: ctor, pos_args: SmallVec::new(), named_args }))
            }
            ConstraintBody::Patterns(terms) => self.build_patterns_lq(terms),
            ConstraintBody::Denial { .. } | ConstraintBody::Aggregation { .. } => None,
        }
    }

    /// Fold a conjunction of patterns into a `LogicalQuery`: empty → `empty_query`,
    /// one → `pattern_query(term: p)`, many → right-nested `conjunction(…)`.
    fn build_patterns_lq(&mut self, patterns: &[TermId]) -> Option<TermId> {
        if patterns.is_empty() {
            let empty = self.logical_query_ctor("empty_query")?;
            return Some(self.kb.alloc(Term::Fn {
                functor: empty,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            }));
        }
        let pattern_ctor = self.logical_query_ctor("pattern_query")?;
        let conj_ctor = self.logical_query_ctor("conjunction")?;
        let term_sym = self.kb.intern("term");
        let left_sym = self.kb.intern("left");
        let right_sym = self.kb.intern("right");
        let mut acc: Option<TermId> = None;
        for &p in patterns.iter().rev() {
            let kb_pattern = self.convert_term(p);
            let pq = self.kb.alloc(Term::Fn {
                functor: pattern_ctor,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(term_sym, kb_pattern)]),
            });
            acc = Some(match acc {
                None => pq,
                Some(rest) => {
                    let mut named_args: SmallVec<[(Symbol, TermId); 2]> =
                        SmallVec::from_slice(&[(left_sym, pq), (right_sym, rest)]);
                    self.kb.canonicalize_record_named_args(conj_ctor, &mut named_args);
                    self.kb.alloc(Term::Fn {
                        functor: conj_ctor,
                        pos_args: SmallVec::new(),
                        named_args,
                    })
                }
            });
        }
        acc
    }

    /// WI-366: surface a value-in-type binding in a sort-relation position
    /// (`sort T = …`, a `requires` / `provides` spec) as a loud load error. The
    /// binding rides faithfully as a `Value::Node` fact, but RESOLVING it (alias
    /// expansion, requires/provides dispatch and coverage) is gated on effect-
    /// expressions-as-types and not yet implemented — so the loader reports it
    /// rather than silently accepting an unenforced / unresolved clause.
    fn diagnose_gated_value_in_type(&mut self, position: &'static str, ty: &TypeExpr) {
        let name = type_expr_base_name(&self.parsed.symbols, ty);
        self.errors.push(LoadError::ValueInTypeNotResolved { position, name });
    }

    /// WI-390: lower a sort-relation spec/target `Value` to a hash-consed `Term`
    /// when it is faithfully term-representable (the universal case, incl. a denoted
    /// value-in-type); otherwise (the opaque residue — never in a spec position)
    /// keep the `Value::Node` carrier and emit the gated "not yet resolved"
    /// diagnostic. Shared by `requires` / `provides` / sort-alias loading.
    fn lower_value_or_gate(
        &mut self,
        value: crate::eval::value::Value,
        position: &'static str,
        ty: &TypeExpr,
    ) -> crate::eval::value::Value {
        match node_occurrence::value_to_term(&mut self.kb, &value) {
            Ok(t) => crate::eval::value::Value::term(t),
            Err(_) => {
                self.diagnose_gated_value_in_type(position, ty);
                value
            }
        }
    }

    fn load_requires_decl(&mut self, r: &RequiresDecl, domain: TermId) {
        let requirement_sort = self.kb.make_name_term("Requirement");
        let requires_sym = self.kb.resolve_symbol("anthill.reflect.SortRequiresInfo");
        let spec_value = self.sort_inst_to_value(&r.type_expr);

        // Named args: sort_ref, spec
        let sort_ref_sym = self.kb.intern("sort_ref");
        let spec_sym = self.kb.intern("spec");
        self.kb.register_entity_fields(requires_sym, vec![sort_ref_sym, spec_sym]);
        // WI-390: a denoted-bearing spec is now faithfully term-representable, so
        // lower it to a `TermId` — the SortRequiresInfo head stays a hash-consed
        // `Term::Fn`, which `direct_requires` reads (no silent skip) and the
        // `resolve_cache` keys on. A ground spec passes through unchanged; only the
        // opaque residue stays a `Value::Node` fact + the gated diagnostic.
        use crate::eval::value::Value;
        let spec_value = self.lower_value_or_gate(spec_value, "requires", &r.type_expr);
        self.kb.assert_metadata_fact_carrier(
            requires_sym,
            Vec::new(),
            vec![(sort_ref_sym, Value::term(domain)), (spec_sym, spec_value)],
            requirement_sort,
            domain,
            None,
        );
    }

    fn load_describe(&mut self, d: &Describe, domain: TermId) {
        let target_term = self.name_to_sort_term(&d.target);
        for content in &d.contents {
            self.emit_desc_fact(target_term, content, domain);
        }
    }

    /// Encode a `ProofStrategy` IR node into a `ProofStrategyKind` (or
    /// `ProofStrategyOpen`) Term. Shared by ProofRecord.strategy and
    /// the per-step / concluding-clause tactic fields of structured
    /// proofs (proposal 031).
    fn encode_strategy(&mut self, s: &ProofStrategy) -> TermId {
        let sname_sym = self.kb.alloc(Term::Const(
            super::term::Literal::String(self.parsed.symbols.name(s.name).to_string())
        ));
        let strat_sym = self.kb.resolve_symbol("anthill.realization.ProofStrategyKind");
        let arg_ids: Vec<TermId> = s.args.iter().map(|&t| self.convert_term(t)).collect();
        let args_list = build_list(self.kb, &arg_ids);
        let name_arg = self.kb.symbols.intern("name");
        let args_arg = self.kb.symbols.intern("args");
        self.kb.alloc(Term::Fn {
            functor: strat_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (name_arg, sname_sym),
                (args_arg, args_list),
            ]),
        })
    }

    /// Resolve a structured-proof cite name to its qualified rule QN.
    /// Step-local labels (matching one of `step_labels`) resolve to
    /// `<parent_proof_qn>.<label>` — phase-b dispatch will look up
    /// the synthesized step rule under that QN. External cites fall
    /// back to scope-aware resolution against the loader's current
    /// scope (same path the parent proof's `using` clause uses).
    /// Names that don't resolve are encoded as their source-side
    /// segment join so the dispatcher can surface a clear error
    /// rather than silently dropping the cite.
    fn resolve_step_cite(
        &mut self,
        name: &Name,
        parent_proof_qn: &str,
        step_labels: &std::collections::BTreeSet<String>,
    ) -> String {
        let source = join_segments(&self.parsed.symbols, &name.segments);
        if step_labels.contains(&source) {
            return format!("{parent_proof_qn}.{source}");
        }
        let sym = self.remap_name(name);
        match self.kb.symbols.get(sym) {
            crate::intern::SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            crate::intern::SymbolDef::Unresolved { .. } => source,
        }
    }

    /// Encode a structured-proof cite-list as a cons-list of String
    /// literals carrying each cite's resolved qualified rule QN
    /// (step-local labels become `<parent_proof_qn>.<label>`; external
    /// names go through scope-aware resolution).
    fn encode_step_using_list(
        &mut self,
        using: &[Name],
        parent_proof_qn: &str,
        step_labels: &std::collections::BTreeSet<String>,
    ) -> TermId {
        let strs: Vec<TermId> = using.iter()
            .map(|n| {
                let qn = self.resolve_step_cite(n, parent_proof_qn, step_labels);
                self.kb.alloc(Term::Const(super::term::Literal::String(qn)))
            })
            .collect();
        build_list(self.kb, &strs)
    }

    /// Encode one structured-proof step rule into a ProofStep Term.
    /// The step's head is taken as the first positive head of the
    /// rule (proposal 031 v0 supports single-head steps); multi-head
    /// or denial steps are encoded with `Bottom` as a placeholder so
    /// the dispatcher can reject them at runtime with a clear error.
    fn encode_proof_step(
        &mut self,
        step: &ProofStep,
        parent_proof_qn: &str,
        step_labels: &std::collections::BTreeSet<String>,
    ) -> TermId {
        let label_str = step.rule.label.as_ref()
            .map(|n| join_segments(&self.parsed.symbols, &n.segments))
            .unwrap_or_default();
        let label_term = self.kb.alloc(Term::Const(
            super::term::Literal::String(label_str)
        ));

        let head_term = match step.rule.heads.first() {
            Some(RuleHead::Term(tid)) => self.convert_term(*tid),
            _ => self.kb.alloc(Term::Bottom),
        };

        let body_ids: Vec<TermId> = step.rule.body.as_ref()
            .map(|terms| terms.iter().map(|&t| self.convert_term(t)).collect())
            .unwrap_or_default();
        let body_list = build_list(self.kb, &body_ids);

        let using_list = self.encode_step_using_list(&step.using, parent_proof_qn, step_labels);
        let tactic_term = self.encode_strategy(&step.strategy);

        let s_sym = self.kb.resolve_symbol("anthill.realization.ProofStep");
        let label_arg = self.kb.symbols.intern("label");
        let head_arg = self.kb.symbols.intern("head_term");
        let body_arg = self.kb.symbols.intern("body_terms");
        let using_arg = self.kb.symbols.intern("using_names");
        let tactic_arg = self.kb.symbols.intern("tactic");
        self.kb.alloc(Term::Fn {
            functor: s_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (label_arg, label_term),
                (head_arg, head_term),
                (body_arg, body_list),
                (using_arg, using_list),
                (tactic_arg, tactic_term),
            ]),
        })
    }

    fn encode_proof_conclude(
        &mut self,
        c: &ConcludeClause,
        parent_proof_qn: &str,
        step_labels: &std::collections::BTreeSet<String>,
    ) -> TermId {
        let using_list = self.encode_step_using_list(&c.using, parent_proof_qn, step_labels);
        let tactic_term = self.encode_strategy(&c.strategy);
        let c_sym = self.kb.resolve_symbol("anthill.realization.ProofConcludeClause");
        let using_arg = self.kb.symbols.intern("using_names");
        let tactic_arg = self.kb.symbols.intern("tactic");
        self.kb.alloc(Term::Fn {
            functor: c_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (using_arg, using_list),
                (tactic_arg, tactic_term),
            ]),
        })
    }

    /// Lower a `proof <target> by <strategy> ... end` declaration into a
    /// ProofRecord fact. The target's qualified name and a term
    /// encoding of strategy/body are written so an external driver
    /// (CLI, IDE) can dispatch without reparsing the source.
    /// WI-539 Part 2: if `target` is a contract-proof target `<op>.<clause>`
    /// (last segment `requires`/`ensures`, the prefix resolving to an
    /// `Operation`), the fully-qualified contract QN `<op-qn>.<clause>`. A
    /// contract clause has no rule symbol of its own, so [`Self::load_proof`]
    /// interns this QN for the `ProofRecord.rule` field directly; the
    /// proof-verification pass (`kb::proof_verify`) splits it back to the op +
    /// clause to discharge it (proposal 025 §"Proof for operation contracts").
    /// `None` for any other target — those keep the normal `remap_name` path.
    fn contract_proof_target_qn(&self, target: &Name) -> Option<String> {
        if target.segments.len() < 2 {
            return None;
        }
        let last = self.parsed.symbols.name(*target.segments.last().unwrap());
        // The clause-keyword set is owned by the verification pass (the single
        // source of truth shared with its inverse split, `proof_verify::contract_target`).
        if !crate::kb::proof_verify::CONTRACT_CLAUSE_KEYWORDS.contains(&last) {
            return None;
        }
        let prefix = &target.segments[..target.segments.len() - 1];
        let prefix_name = join_segments(&self.parsed.symbols, prefix);
        let op_sym = resolve_name_in_kb_opt(&self.kb, &prefix_name, self.current_scope.raw())?;
        if self.kb.kind_of(op_sym) != Some(SymbolKind::Operation) {
            return None;
        }
        Some(format!("{}.{}", self.kb.qualified_name_of(op_sym), last))
    }

    fn load_proof(&mut self, p: &ProofDecl, domain: TermId) {
        // WI-539 Part 2: a contract-proof target `<op>.<clause>` (proposal 025
        // §"Proof for operation contracts") has no rule symbol of its own to
        // resolve — intern its fully-qualified contract QN directly so the
        // ProofRecord loads (the proof-verification pass re-derives the operation
        // from the QN and discharges against its body), instead of letting
        // `remap_name` raise a spurious UnresolvedName. A non-contract target
        // keeps the unchanged `remap_name` path.
        let target_sym = match self.contract_proof_target_qn(&p.target) {
            Some(qn) => self.kb.symbols.intern(&qn),
            None => self.remap_name(&p.target),
        };

        let strategy_term = match &p.strategy {
            None => {
                let open_sym = self.kb.resolve_symbol("anthill.realization.ProofStrategyOpen");
                self.kb.alloc(Term::Fn {
                    functor: open_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::new(),
                })
            }
            Some(s) => self.encode_strategy(s),
        };

        let body_term = match &p.body {
            None => {
                let none_sym = self.kb.resolve_symbol("anthill.realization.ProofBodyNone");
                self.kb.alloc(Term::Fn {
                    functor: none_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::new(),
                })
            }
            Some(ProofBody::Hints(hints)) => {
                let hint_ids: Vec<TermId> = hints.iter().map(|&t| self.convert_term(t)).collect();
                let list = build_list(self.kb, &hint_ids);
                let h_sym = self.kb.resolve_symbol("anthill.realization.ProofBodyHints");
                let hints_arg = self.kb.symbols.intern("hints");
                self.kb.alloc(Term::Fn {
                    functor: h_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (hints_arg, list),
                    ]),
                })
            }
            Some(ProofBody::Structured { steps, conclude }) => {
                // Collect step labels first so step-internal cites
                // (`using h1, h2, ...` referencing other steps in
                // this same body) resolve to `<parent_proof_qn>.<label>`
                // rather than going through scope-aware lookup. The
                // parent_proof_qn is the qualified name of the rule
                // being proved (`rule_text`, computed below before
                // ProofRecord construction).
                let parent_proof_qn: String = match self.kb.symbols.get(target_sym) {
                    crate::intern::SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                    crate::intern::SymbolDef::Unresolved { name } => name.clone(),
                };
                let step_labels: std::collections::BTreeSet<String> = steps.iter()
                    .filter_map(|s| s.rule.label.as_ref()
                        .map(|n| join_segments(&self.parsed.symbols, &n.segments)))
                    .collect();
                let step_terms: Vec<TermId> = steps.iter()
                    .map(|s| self.encode_proof_step(s, &parent_proof_qn, &step_labels))
                    .collect();
                let steps_list = build_list(self.kb, &step_terms);
                let conclude_term = match conclude {
                    Some(c) => self.encode_proof_conclude(c, &parent_proof_qn, &step_labels),
                    None => self.kb.alloc(Term::Bottom),
                };
                let s_sym = self.kb.resolve_symbol("anthill.realization.ProofBodyStructured");
                let steps_arg = self.kb.symbols.intern("steps");
                let conclude_arg = self.kb.symbols.intern("conclude");
                self.kb.alloc(Term::Fn {
                    functor: s_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (steps_arg, steps_list),
                        (conclude_arg, conclude_term),
                    ]),
                })
            }
            Some(ProofBody::Query { text, mapping }) => {
                let text_term = self.kb.alloc(Term::Const(
                    super::term::Literal::String(text.clone())
                ));
                let mapping_term = match mapping {
                    None => {
                        let nil_sym = self.kb.resolve_symbol("anthill.prelude.List.nil");
                        self.kb.alloc(Term::Fn {
                            functor: nil_sym,
                            pos_args: SmallVec::new(),
                            named_args: SmallVec::new(),
                        })
                    }
                    Some(mb) => {
                        let pair_sym = self.kb.resolve_symbol("anthill.realization.MappingEntry");
                        let s_arg = self.kb.symbols.intern("source");
                        let t_arg = self.kb.symbols.intern("target");
                        let entries: Vec<TermId> = mb.entries.iter().map(|e| {
                            let src = self.kb.alloc(Term::Const(
                                super::term::Literal::String(join_segments(&self.parsed.symbols, &e.source.segments))
                            ));
                            let tgt = self.kb.alloc(Term::Const(
                                super::term::Literal::String(e.target.clone())
                            ));
                            self.kb.alloc(Term::Fn {
                                functor: pair_sym,
                                pos_args: SmallVec::new(),
                                named_args: SmallVec::from_slice(&[
                                    (s_arg, src),
                                    (t_arg, tgt),
                                ]),
                            })
                        }).collect();
                        build_list(self.kb, &entries)
                    }
                };
                let q_sym = self.kb.resolve_symbol("anthill.realization.ProofBodyQuery");
                let text_arg = self.kb.symbols.intern("text");
                let map_arg = self.kb.symbols.intern("mapping");
                self.kb.alloc(Term::Fn {
                    functor: q_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (text_arg, text_term),
                        (map_arg, mapping_term),
                    ]),
                })
            }
        };

        let record_sym = self.kb.resolve_symbol("anthill.realization.ProofRecord");
        let rule_arg = self.kb.symbols.intern("rule");
        let strategy_arg = self.kb.symbols.intern("strategy");
        let body_arg = self.kb.symbols.intern("body");
        let result_arg = self.kb.symbols.intern("result");
        let deps_arg = self.kb.symbols.intern("dependencies");
        let using_arg = self.kb.symbols.intern("using");
        // Phase α.2 — proposal 030: witness, state_hash, parametric_context.
        // At load time these are placeholders; the prove driver will
        // populate them when a successful discharge produces a witness
        // (phase α.3+). Until then a Pending record carries a
        // TrustedAxiom placeholder so the field is always populated.
        let witness_arg = self.kb.symbols.intern("witness");
        let state_hash_arg = self.kb.symbols.intern("state_hash");
        let parametric_context_arg = self.kb.symbols.intern("parametric_context");

        let rule_text = match self.kb.symbols.get(target_sym) {
            SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            SymbolDef::Unresolved { name } => name.clone(),
        };
        let rule_term = self.kb.alloc(Term::Const(
            super::term::Literal::String(rule_text)
        ));
        let pending_sym = self.kb.resolve_symbol("anthill.realization.ObligationStatus.Pending");
        let pending_term = self.kb.alloc(Term::Fn {
            functor: pending_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let nil_sym = self.kb.resolve_symbol("anthill.prelude.List.nil");
        let nil_term = self.kb.alloc(Term::Fn {
            functor: nil_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });

        // `using` clause: each cited name is resolved against the
        // proof block's enclosing scope (so `using lemma_a` works
        // bare, and `using anthill.x.lemma_a` also works). Resolved
        // qualified names land as String consts in a cons-list, so
        // the CLI driver can read them without re-parsing.
        let using_qns: Vec<TermId> = p.using.iter().map(|n| {
            let sym = self.remap_name(n);
            let qn = match self.kb.symbols.get(sym) {
                SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                SymbolDef::Unresolved { name } => name.clone(),
            };
            self.kb.alloc(Term::Const(super::term::Literal::String(qn)))
        }).collect();
        let using_list = build_list(self.kb, &using_qns);

        // Phase α.2 placeholder values for witness, state_hash, and
        // parametric_context. A Pending ProofRecord carries
        // TrustedAxiom(reason: "pending — not yet discharged") as its
        // witness placeholder so the field is always populated. The
        // prove driver overwrites this when a tactic returns a real
        // witness (phase α.3+).
        let trusted_axiom_sym =
            self.kb.resolve_symbol("anthill.realization.witness.ProofWitness.TrustedAxiom");
        let reason_arg = self.kb.symbols.intern("reason");
        let pending_reason_term = self.kb.alloc(Term::Const(
            super::term::Literal::String("pending — not yet discharged".to_string())
        ));
        let placeholder_witness = self.kb.alloc(Term::Fn {
            functor: trusted_axiom_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(reason_arg, pending_reason_term)]),
        });
        let empty_state_hash = self.kb.alloc(Term::Const(
            super::term::Literal::String(String::new())
        ));

        let record_term = self.kb.alloc(Term::Fn {
            functor: record_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (rule_arg, rule_term),
                (strategy_arg, strategy_term),
                (body_arg, body_term),
                (result_arg, pending_term),
                (deps_arg, nil_term),
                (using_arg, using_list),
                (witness_arg, placeholder_witness),
                (state_hash_arg, empty_state_hash),
                (parametric_context_arg, nil_term),
            ]),
        });
        let record_sort = self.kb.make_name_term("anthill.realization.ProofRecord");
        self.kb.assert_metadata_fact(record_term, record_sort, domain, None);
    }

    /// `provides Spec[...]` inside a sort body. Emits a
    /// `SortProvidesInfo` fact recording the user's intent ("this
    /// sort claims to satisfy the named spec at the given binding").
    /// The verification pass `register_provides_specializations`
    /// (proposal 030 phase α.8 / WI-119 Variant 3) walks these
    /// facts after α.6/α.7 have registered the requires-clause
    /// witnesses; for each it checks that every requires-law has
    /// a Discharged ProofRecord at the substitution and emits
    /// `Specialization` ProofRecords pointing at the supporting
    /// proofs.
    fn load_provides_clause(&mut self, pc: &ProvidesClause, domain: TermId) {
        let provides_sort = self.kb.make_name_term("Requirement");
        let provides_sym = self.kb.resolve_symbol("anthill.reflect.SortProvidesInfo");
        let spec_value = self.sort_inst_to_value(&pc.spec);

        let sort_ref_sym = self.kb.intern("sort_ref");
        let spec_sym = self.kb.intern("spec");
        self.kb.register_entity_fields(provides_sym, vec![sort_ref_sym, spec_sym]);
        // WI-390: lower a denoted-bearing spec to a `TermId` (mirrors
        // load_requires_decl) so the SortProvidesInfo head stays a hash-consed
        // `Term::Fn` — keeping requires/provides symmetric for
        // `check_provider_requires`.
        use crate::eval::value::Value;
        let spec_value = self.lower_value_or_gate(spec_value, "provides", &pc.spec);
        self.kb.assert_metadata_fact_carrier(
            provides_sym,
            Vec::new(),
            vec![(sort_ref_sym, Value::term(domain)), (spec_sym, spec_value)],
            provides_sort,
            domain,
            None,
        );
    }

    /// Standalone `provides Spec language X ... end`. Proposal 038.
    ///
    /// Inner facts/rules/proofs are loaded against the spec sort as their
    /// domain — so a `fact Eq[T = Int64]` inside `provides Int64 language rust`
    /// triggers Phase 1's SortProvidesInfo auto-emit through the sort-body
    /// path, recording the carrier as the spec sort symbol (not a namespace
    /// doppelgänger). For non-anthill languages, additionally emit an
    /// `Implementation` fact (anthill.realization.Implementation) carrying
    /// the carrier/artifact/namespace-map metadata so codegen and
    /// interpreters can locate the host bindings by `(language, profile)`.
    fn load_provides_block(&mut self, pb: &ProvidesBlock, _domain: TermId) {
        // The provides-block spec is used only as a ground scope identity (and the
        // `Implementation` fact target), so it needs a `TermId`. WI-366: a
        // denoted-bearing spec (a value-in-type binding, e.g. `Foo[Int64, 3]`)
        // projects to its base sort here — the faithful value-in-type rides on a
        // fact, not a scope identity. (Replaces `sort_inst_to_term`, whose
        // `as_term().expect(...)` would panic on a value spec — reachable from the
        // valid syntax `provides Foo[Int64, 3] language … end`.)
        let spec_term = match self.sort_inst_to_value(&pb.spec) {
            crate::eval::value::Value::Term { id: t, .. } => t,
            _ => {
                self.diagnose_gated_value_in_type("provides", &pb.spec);
                match &pb.spec {
                    TypeExpr::Simple(name) | TypeExpr::Parameterized { name, .. } => {
                        self.name_to_sort_term(name)
                    }
                    _ => self.kb.make_name_term("?"),
                }
            }
        };
        let prev_scope = self.current_scope;
        self.current_scope = spec_term;

        for item in &pb.items {
            match item {
                ProvidesItem::Rule(r) => self.load_rule(r, spec_term),
                ProvidesItem::RuleBlock(rb) => {
                    for r in &rb.entries { self.load_rule(r, spec_term); }
                }
                ProvidesItem::Fact(f) => self.load_fact(f, spec_term),
                ProvidesItem::Proof(p) => self.load_proof(p, spec_term),
                ProvidesItem::Artifact(_)
                | ProvidesItem::Carrier(_)
                | ProvidesItem::NamespaceMap(_) => {}
            }
        }

        self.current_scope = prev_scope;

        if self.parsed.symbols.name(pb.language) != "anthill" {
            self.emit_implementation_fact(pb, spec_term);
        }
    }

    /// Build and assert an `anthill.realization.Implementation` fact from
    /// a `provides Spec language X ... end` block. Populates target,
    /// artifact, language, profile, carrier, and namespace_map fields per
    /// the entity definition in stdlib/anthill/realization/realization.anthill.
    fn emit_implementation_fact(&mut self, pb: &ProvidesBlock, spec_term: TermId) {
        // target: qualified name of the spec sort, as a String literal.
        let spec_functor = match self.kb.get_term(spec_term) {
            Term::Fn { functor, .. } => *functor,
            _ => return,
        };
        let target_qn = match self.kb.symbols.get(spec_functor) {
            SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            SymbolDef::Unresolved { name } => name.clone(),
        };
        let target_term = self.kb.alloc(Term::Const(
            super::term::Literal::String(target_qn.clone())));

        // language: from pb.language (parsed-symbol → string).
        let language_str = self.parsed.symbols.name(pb.language).to_string();
        let language_term = self.kb.alloc(Term::Const(
            super::term::Literal::String(language_str)));

        // artifact: first Artifact item, defaulting to "" if absent.
        let artifact_str = pb.items.iter().find_map(|item| match item {
            ProvidesItem::Artifact(s) => Some(s.clone()),
            _ => None,
        }).unwrap_or_default();
        let artifact_term = self.kb.alloc(Term::Const(
            super::term::Literal::String(artifact_str)));

        // profile and description default to none (Option[T = String]).
        let none_sym = self.kb.resolve_symbol("anthill.prelude.Option.none");
        let none_term = self.kb.alloc(Term::Fn {
            functor: none_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
        });

        // carrier: cons-list of CarrierBinding terms collected from each
        // `carrier` clause inside the block.
        let cb_sym = self.kb.resolve_symbol("anthill.realization.CarrierBinding");
        let sort_name_arg = self.kb.intern("sort_name");
        let host_type_arg = self.kb.intern("host_type");
        let mut carrier_terms: Vec<TermId> = Vec::new();
        for item in &pb.items {
            if let ProvidesItem::Carrier(bindings) = item {
                for b in bindings {
                    let sort_name = self.parsed.symbols.name(b.anthill_param).to_string();
                    let sort_name_term = self.kb.alloc(Term::Const(
                        super::term::Literal::String(sort_name)));
                    let host_type_term = self.host_type_to_string_term(b.host_type);
                    carrier_terms.push(self.kb.alloc(Term::Fn {
                        functor: cb_sym,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::from_slice(&[
                            (sort_name_arg, sort_name_term),
                            (host_type_arg, host_type_term),
                        ]),
                    }));
                }
            }
        }
        let carrier_list = build_list(self.kb, &carrier_terms);

        // namespace_map: cons-list of NamespaceMapping terms.
        let nm_sym = self.kb.resolve_symbol("anthill.realization.NamespaceMapping");
        let ns_arg = self.kb.intern("namespace");
        let host_module_arg = self.kb.intern("host_module");
        let mut nm_terms: Vec<TermId> = Vec::new();
        for item in &pb.items {
            if let ProvidesItem::NamespaceMap(entries) = item {
                for e in entries {
                    let ns_name = self.parsed.symbols.name(e.anthill_namespace).to_string();
                    let ns_name_term = self.kb.alloc(Term::Const(
                        super::term::Literal::String(ns_name)));
                    let host_mod_term = self.host_type_to_string_term(e.host_module);
                    nm_terms.push(self.kb.alloc(Term::Fn {
                        functor: nm_sym,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::from_slice(&[
                            (ns_arg, ns_name_term),
                            (host_module_arg, host_mod_term),
                        ]),
                    }));
                }
            }
        }
        let nm_list = build_list(self.kb, &nm_terms);

        // Assemble the Implementation fact.
        let impl_sym = self.kb.resolve_symbol("anthill.realization.Implementation");
        let target_arg = self.kb.intern("target");
        let artifact_arg = self.kb.intern("artifact");
        let language_arg = self.kb.intern("language");
        let profile_arg = self.kb.intern("profile");
        let description_arg = self.kb.intern("description");
        let carrier_arg = self.kb.intern("carrier");
        let nm_field = self.kb.intern("namespace_map");

        let impl_term = self.kb.alloc(Term::Fn {
            functor: impl_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (target_arg, target_term),
                (artifact_arg, artifact_term),
                (language_arg, language_term),
                (profile_arg, none_term),
                (description_arg, none_term),
                (carrier_arg, carrier_list),
                (nm_field, nm_list),
            ]),
        });
        let impl_sort = self.kb.make_name_term("anthill.realization.Implementation");
        self.kb.assert_metadata_fact(impl_term, impl_sort, spec_term, None);
    }

    /// Convert a parsed host_type term (typically a `Term::Const(String)`
    /// like `"i64"`) into a String-literal KB term. Falls back to
    /// stringifying via `convert_term` for non-literal forms.
    fn host_type_to_string_term(&mut self, parse_id: TermId) -> TermId {
        if let Term::Const(super::term::Literal::String(s)) = self.parsed.terms.get(parse_id) {
            let s = s.clone();
            return self.kb.alloc(Term::Const(super::term::Literal::String(s)));
        }
        self.convert_term(parse_id)
    }

    fn emit_desc_fact(&mut self, target: TermId, text: &str, domain: TermId) {
        let desc_sort = self.kb.make_name_term("Description");
        let desc_sym = self.kb.resolve_symbol("Description");
        let text_term = self.kb.alloc(Term::Const(super::term::Literal::String(text.to_string())));

        // Track description index per target
        let idx = self.desc_index.entry(target.raw()).or_insert(0);
        let index_term = self.kb.alloc(Term::Const(super::term::Literal::Int(*idx)));
        *idx += 1;

        let desc_fact = self.kb.alloc(Term::Fn {
            functor: desc_sym,
            pos_args: SmallVec::from_slice(&[target, text_term, index_term]),
            named_args: SmallVec::new(),
        });
        self.kb.assert_metadata_fact(desc_fact, desc_sort, domain, None);
    }

    /// Convert a list of clauses (each a Vec<TermId>) into a cons-list.
    /// Multi-goal clauses are wrapped in a conjunction term.
    /// WI-552: canonicalize binder/parameter occurrences in a converted clause
    /// or guard goal to `var_ref(name)`. The op's signature places (parameters +
    /// `result`, held in [`Self::signature_place_types`] for the signature being
    /// loaded) are the only variables a `requires`/`ensures` clause or a
    /// signature-level guard can reference, so wrapping exactly those symbols is
    /// both correct and precise — a `const`/global ref stays a decidable bare
    /// `Ref`. See [`wrap_places_as_var_ref`].
    fn var_ref_signature_places(&mut self, term: TermId) -> TermId {
        if self.signature_place_types.is_empty() {
            return term;
        }
        let places: HashSet<Symbol> = self.signature_place_types.keys().copied().collect();
        let var_ref_sym = self.kb.resolve_symbol("anthill.reflect.Expr.var_ref");
        wrap_places_as_var_ref(&mut self.kb, term, &places, var_ref_sym)
    }

    fn convert_clause_list(&mut self, clauses: &[Vec<TermId>]) -> TermId {
        self.convert_clause_list_with_extra(clauses, &[])
    }

    /// Like `convert_clause_list`, plus a tail of additional kb-space clause
    /// terms to append after the user-written clauses. The `extra_terms` are
    /// already-built kb TermIds (one term per clause, no conjunction wrap),
    /// used by WI-320's auto-requires inference to append synthesized
    /// `EffectsRuntime[Effects = E_i]` clauses to a user's requires list.
    fn convert_clause_list_with_extra(
        &mut self,
        clauses: &[Vec<TermId>],
        extra_terms: &[TermId],
    ) -> TermId {
        let mut clause_terms: Vec<TermId> = clauses
            .iter()
            .map(|clause| {
                // WI-552: canonicalize each goal's param/`result` refs to var_ref
                // at the producer, so the stored clause carries the binder as the
                // variable it is (the discharge-time normalize pass is retired).
                let goal_terms: Vec<TermId> = clause
                    .iter()
                    .map(|&tid| {
                        let t = self.convert_term(tid);
                        self.var_ref_signature_places(t)
                    })
                    .collect();
                if goal_terms.len() == 1 {
                    goal_terms[0]
                } else {
                    let conj_sym = self.kb.intern("conjunction");
                    self.kb.alloc(Term::Fn {
                        functor: conj_sym,
                        pos_args: SmallVec::from_vec(goal_terms),
                        named_args: SmallVec::new(),
                    })
                }
            })
            .collect();
        clause_terms.extend_from_slice(extra_terms);
        build_list(self.kb, &clause_terms)
    }

    /// WI-320 / proposal 045 §6 Phase 0 — auto-requires inference for an
    /// operation's `effects <expr>` clause.
    ///
    /// Walks the operation's effects and emits one `EffectsRuntime[Effects = E_i]`
    /// kb term per distinct free row variable. The OperationInfo.requires list
    /// then contains the synthesized clauses alongside user-written ones —
    /// avoiding boilerplate at every operation declaration that mentions a
    /// row variable.
    ///
    /// **Heuristic for "free row variable":** the current `_effect_set`
    /// grammar admits `simple_type | application | variable_term`. Only the
    /// bare `simple_type` form (`effects E`) can name a row variable; both
    /// `application` (`Modify[T]` — closed) and `variable_term` (`?x` —
    /// reserved for term-level variables, not row vars at the type level)
    /// short-circuit. A bare name qualifies as a row variable when its
    /// resolved symbol participates in a `SortAlias(<sym>, Var)` fact —
    /// shorthand for "declared as `sort X = ?`", which is exactly the shape
    /// the `effects X` sugar (this WI's `effects_sort_item`) desugars to and
    /// the shape pre-existing migration sites (Function.E, Stream.E, etc.)
    /// already had. Concrete effect sorts like `Suspension`/`Branch` lack
    /// the SortAlias fact and are rightly excluded.
    ///
    /// **Per-spec examples:**
    ///   - `effects E`                  → one requires
    ///   - `effects merge(E1, E2)`      → two requires  (forward-looking;
    ///                                     the current grammar's
    ///                                     `_effect_set` does not yet admit
    ///                                     row-combinator applications, so
    ///                                     this case is a no-op today)
    ///   - `effects { E, -Modify[kb] }` → one requires  (E only)
    ///   - `effects { Modify[c] }`      → none          (closed row)
    ///
    /// The kb term emitted per row variable is the SortAlias-backed Var
    /// shape that the structural type lowering (`type_expr_to_value`)
    /// returns for the effect — the same
    /// Term that goes into OperationInfo.effects, keeping the row var's
    /// identity consistent across effects/requires. This is structurally
    /// distinct from what a hand-written `requires EffectsRuntime[Effects = E]`
    /// lowers to (which routes through convert_instantiation_term →
    /// convert_type_value and produces a `Term::Ref(E_sym)` value, not the
    /// SortAlias Var). Both shapes happen to unify against the bridge fact
    /// head `EffectsRuntime[Effects = effects_rows(?expr)]` — the Var/Ref
    /// query-side binds to the effects_rows subterm via the discrim tree's
    /// standard Var-skip path — but they are NOT interchangeable Terms,
    /// despite the symmetry the surface syntax suggests.
    fn infer_effects_row_requires(&mut self, o: &Operation) -> Vec<TermId> {
        // EffectsRuntime is unconditionally pre-registered by
        // `register_stdlib_scopes` (and the bridge fact emission at
        // `emit_effects_runtime_bridge_fact` `.expect()`s the same symbol).
        // A missing symbol here is the same bootstrap regression as the
        // bridge-fact path — surface it loudly rather than silently dropping
        // every operation's auto-requires (which would mask the upstream
        // failure behind confusing per-operation 'requires unmet' errors).
        // Matches code-review #9's policy from commit 9ed183d.
        let er_sym = self.kb.try_resolve_symbol("anthill.prelude.EffectsRuntime").expect(
            "WI-320 bootstrap invariant: anthill.prelude.EffectsRuntime symbol \
             pre-registered by register_stdlib_scopes — see kb/load.rs",
        );
        let effects_param_sym = self.kb.intern("Effects");

        let mut seen: HashSet<Symbol> = HashSet::new();
        let mut result: Vec<TermId> = Vec::new();
        for eff in &o.effects {
            let TypeExpr::Simple(name) = &eff.type_expr else {
                continue;
            };
            // WI-396: a MULTI-segment effect name is an expression-carried
            // projection (`effects s.E`) or a qualified ref, never a bare
            // row-variable (which is always a single-segment `sort E = ?` name).
            // Skip it BEFORE `remap_name`, which would join the segments
            // (`"s.E"`) and raise a spurious `UnresolvedName` — the projection is
            // classified + eliminated on the `type_expr_to_value` path, not here.
            if name.segments.len() >= 2 {
                continue;
            }
            // Cache the resolved sym to avoid pushing duplicate UnresolvedName
            // diagnostics: `remap_name` errors-on-miss, so calling it once
            // here AND again via `type_expr_to_value` (~7067) would double a
            // legitimate error. We resolve once, dedup-by-sym, then reuse the
            // SortAlias Var directly without re-routing through remap_name.
            let sym = self.remap_name(name);
            if !seen.insert(sym) {
                continue;
            }
            // Row-variable test: must be backed by a SortAlias fact. Skipping
            // here also skips the second `remap_name` call below for non-row
            // effects (concrete sorts like `Suspension`).
            let Some(row_var_term) = self.find_sort_alias_var(sym) else {
                continue;
            };
            let er_term = self.kb.alloc(Term::Fn {
                functor: er_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(effects_param_sym, row_var_term)]),
            });
            result.push(er_term);
        }
        result
    }

    // ── Member fact emission ───────────────────────────────────

    fn emit_member_fact(&mut self, name_sym: Symbol, kind_str: &str, parent: TermId) {
        let member_sym = self.kb.resolve_symbol("anthill.reflect.member");
        let member_sort = self.kb.make_name_term("Member");
        let name_term = self.kb.make_name_term_from_sym(name_sym);
        let kind_sym = self.kb.intern(kind_str);
        let kind_term = self.kb.alloc(Term::Ident(kind_sym));
        let member_term = self.kb.alloc(Term::Fn {
            functor: member_sym,
            pos_args: SmallVec::from_slice(&[name_term, kind_term, parent]),
            named_args: SmallVec::new(),
        });
        self.kb.assert_metadata_fact(member_term, member_sort, parent, None);
    }

    fn emit_member_facts_for_items(&mut self, items: &[Item], parent: TermId) {
        for item in items {
            match item {
                Item::Entity(e) => {
                    let sym = self.remap_name(&e.name);
                    self.emit_member_fact(sym, "Constructor", parent);
                }
                Item::AbstractSort(s) => {
                    let sym = self.remap_name(&s.name);
                    self.emit_member_fact(sym, "Sort", parent);
                }
                Item::SortWithBody(s) => {
                    let sym = self.remap_name(&s.name);
                    let kind = if s.kind == SortDeclKind::Enum { "Enum" } else { "Sort" };
                    self.emit_member_fact(sym, kind, parent);
                }
                Item::Operation(o) => {
                    let sym = self.remap_name(&o.name);
                    self.emit_member_fact(sym, "Operation", parent);
                }
                Item::OperationBlock(ob) => {
                    for op in &ob.entries {
                        let sym = self.remap_name(&op.name);
                        self.emit_member_fact(sym, "Operation", parent);
                    }
                }
                Item::Rule(r) => {
                    if let Some(ref label) = r.label {
                        let sym = self.remap_name(label);
                        self.emit_member_fact(sym, "Rule", parent);
                    }
                }
                Item::RuleBlock(rb) => {
                    for rule in &rb.entries {
                        if let Some(ref label) = rule.label {
                            let sym = self.remap_name(label);
                            self.emit_member_fact(sym, "Rule", parent);
                        }
                    }
                }
                Item::Namespace(n) => {
                    let sym = self.remap_name(&n.name);
                    self.emit_member_fact(sym, "Namespace", parent);
                }
                // Proposal 039 / WI-084: a `const` emits no scope-member fact yet.
                // Reflection of consts (a `member(Name, "Const", Parent)` fact, or
                // a `ConstInfo` value fact) is deferred to the resolution/typing
                // phase that actually consumes it — see the `const_types` note in
                // kb/mod.rs. Made explicit (not swept into `_`) so the deferral is
                // visible at the site, per the repo's loud-over-silent rule.
                Item::Const(_) => {}
                _ => {}
            }
        }
    }

    fn load_meta_block(&mut self, mb: &MetaBlock) -> TermId {
        let meta_sym = self.kb.resolve_symbol("meta");
        let named_args: SmallVec<[(Symbol, TermId); 2]> = mb.entries
            .iter()
            .map(|e| {
                let key_sym = self.reintern(e.key.last());
                let val = self.convert_term(e.value);
                (key_sym, val)
            })
            .collect();
        self.kb.alloc(Term::Fn {
            functor: meta_sym,
            pos_args: SmallVec::new(),
            named_args,
        })
    }
}

#[cfg(test)]
mod wi351_place_tests {
    //! WI-352 — `scan_operation_params` classifies every operation-frame place
    //! by its `SymbolKind`: op params (`Param`), callback params
    //! (`CallbackParam`), callback results (`CallbackResult`), the reserved
    //! `result` (`OpResult`). `provenance` and `is_result_binder` are functions
    //! of this kind (no side-table). Public *resolution* is also covered by
    //! `tests/include/wi351_callback_place_test.rs`.
    use super::{load, register_prelude, NullResolver};
    use crate::intern::SymbolKind;
    use crate::kb::KnowledgeBase;
    use crate::parse;

    /// Load a self-contained snippet off the bare prelude. Mirrors
    /// `wi355_arrow_param_names_lowered_to_named_tuple`: a bodyless op with
    /// concrete (`Int64`/`Bool`) arrow params loads cleanly without the stdlib.
    fn load_op(src: &str) -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        kb.register_standard_builtins();
        let parsed = parse::parse(src).expect("parse");
        load(&mut kb, &parsed, &NullResolver).expect("load");
        kb
    }

    /// Foldleft-shaped op `reduce(z, f: (a, t) -> _) -> _`: op params are
    /// `Param` (= input places), the callback's params/result get
    /// `CallbackParam` / `CallbackResult`, and the reserved `result` is the
    /// sole `OpResult` — so `is_result_binder` (and thus `Cell.new.result`
    /// masking, WI-314) is unchanged.
    #[test]
    fn callback_places_classified_by_kind() {
        let kb = load_op("operation reduce(z: Int64, f: (a: Int64, t: Int64) -> Int64) -> Int64\n");

        let place = |qn: &str| -> SymbolKind {
            let sym = kb
                .try_resolve_symbol(qn)
                .unwrap_or_else(|| panic!("place `{qn}` should resolve"));
            kb.kind_of(sym)
                .unwrap_or_else(|| panic!("place `{qn}` should carry a kind"))
        };

        // Op params → Param (an op param is its own input place).
        assert_eq!(place("reduce.z"), SymbolKind::Param);
        assert_eq!(place("reduce.f"), SymbolKind::Param);
        // Callback params (read off the arrow's named params, WI-355).
        assert_eq!(place("reduce.f.a"), SymbolKind::CallbackParam);
        assert_eq!(place("reduce.f.t"), SymbolKind::CallbackParam);
        // Callback result.
        assert_eq!(place("reduce.f.result"), SymbolKind::CallbackResult);
        // The op's reserved result — the sole OpResult (proposal 041).
        assert_eq!(place("reduce.result"), SymbolKind::OpResult);

        // `is_result_binder` is exactly the OpResult slice: only the op result
        // is a binder; inputs and callback places are not.
        let sym = |qn: &str| kb.try_resolve_symbol(qn).unwrap();
        assert!(kb.is_result_binder(sym("reduce.result")));
        assert!(!kb.is_result_binder(sym("reduce.z")));
        assert!(!kb.is_result_binder(sym("reduce.f")));
        assert!(!kb.is_result_binder(sym("reduce.f.a")));
        assert!(!kb.is_result_binder(sym("reduce.f.result")));
    }

    /// A *single*-param callback registers its sole param and result.
    /// `scan_operation_params` matches the parse-IR `TypeExpr::Arrow` regardless
    /// of arity — single-param arrows lower to the param type *directly* (not a
    /// named tuple, WI-355), but the place names come off the IR, so the
    /// lowering shape is irrelevant. Named single-param arrows parse since
    /// WI-358 (`(x: Int64) -> Bool` → `findp.p.x`); an unnamed one falls back to
    /// the 1-based `_1`.
    #[test]
    fn single_param_callback_place() {
        // Named single param (WI-358): the place takes the declared name.
        let kb = load_op("operation findp(p: (x: Int64) -> Bool) -> Bool\n");
        let role = |qn: &str| kb.try_resolve_symbol(qn).and_then(|s| kb.kind_of(s));
        assert_eq!(role("findp.p.x"), Some(SymbolKind::CallbackParam));
        assert_eq!(role("findp.p.result"), Some(SymbolKind::CallbackResult));

        // Unnamed single param: 1-based positional fallback.
        let kb = load_op("operation g(p: (Int64) -> Bool) -> Bool\n");
        let role = |qn: &str| kb.try_resolve_symbol(qn).and_then(|s| kb.kind_of(s));
        assert_eq!(role("g.p._1"), Some(SymbolKind::CallbackParam));
        assert_eq!(role("g.p.result"), Some(SymbolKind::CallbackResult));
    }

    /// Unnamed callback params fall back to the **1-based** positional names
    /// `_1`, `_2`, … matching the arrow-type lowering (spec §4.5) — never
    /// 0-based, and no spurious `_3` for a two-param arrow.
    #[test]
    fn unnamed_callback_params_are_one_based() {
        let kb = load_op("operation app(f: (Int64, Int64) -> Int64) -> Int64\n");
        let role = |qn: &str| kb.try_resolve_symbol(qn).and_then(|s| kb.kind_of(s));
        assert_eq!(role("app.f._1"), Some(SymbolKind::CallbackParam));
        assert_eq!(role("app.f._2"), Some(SymbolKind::CallbackParam));
        assert_eq!(role("app.f.result"), Some(SymbolKind::CallbackResult));
        assert_eq!(role("app.f._0"), None, "naming is 1-based, not 0-based");
        assert_eq!(role("app.f._3"), None, "only two params");
    }

    /// A callback param or result that is *itself* an arrow is descended into,
    /// so arbitrarily nested callbacks resolve with the position-kind roles at
    /// every depth. `hof(f: (g: (Int64, Int64) -> Int64, y: Int64) -> Int64)` nests a
    /// callback `g` inside `f`'s params; `curry(f: (Int64) -> (Int64) -> Bool)`
    /// nests one in `f`'s result.
    #[test]
    fn nested_callbacks_register_places_recursively() {
        // Param nesting: `f`'s first param `g` is itself a 2-arg callback.
        let kb = load_op("operation hof(f: (g: (Int64, Int64) -> Int64, y: Int64) -> Int64) -> Int64\n");
        let role = |qn: &str| kb.try_resolve_symbol(qn).and_then(|s| kb.kind_of(s));
        assert_eq!(role("hof.f"), Some(SymbolKind::Param));
        assert_eq!(role("hof.f.g"), Some(SymbolKind::CallbackParam));
        assert_eq!(role("hof.f.y"), Some(SymbolKind::CallbackParam));
        assert_eq!(role("hof.f.result"), Some(SymbolKind::CallbackResult));
        // The nested callback `g`'s own params/result, one level deeper.
        assert_eq!(role("hof.f.g._1"), Some(SymbolKind::CallbackParam));
        assert_eq!(role("hof.f.g._2"), Some(SymbolKind::CallbackParam));
        assert_eq!(role("hof.f.g.result"), Some(SymbolKind::CallbackResult));

        // Result nesting: a curried op — `f`'s result is itself a callback.
        let kb = load_op("operation curry(f: (Int64) -> (Int64) -> Bool) -> Bool\n");
        let role = |qn: &str| kb.try_resolve_symbol(qn).and_then(|s| kb.kind_of(s));
        assert_eq!(role("curry.f._1"), Some(SymbolKind::CallbackParam));
        assert_eq!(role("curry.f.result"), Some(SymbolKind::CallbackResult));
        // The result-callback's own param/result, two dots deep.
        assert_eq!(role("curry.f.result._1"), Some(SymbolKind::CallbackParam));
        assert_eq!(role("curry.f.result.result"), Some(SymbolKind::CallbackResult));
    }
}

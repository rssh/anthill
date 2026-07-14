//! Tree-walking interpreter for anthill expression bodies. Proposal 026.
//!
//! Supports: literals, variables, `if`, `let`, operation call, pattern
//! match, lambda + closures, list / tuple literals. Streams and effect
//! handlers are deferred.

pub mod builtins;
pub mod cell_arena;
pub mod closure;
pub mod effects;
pub mod error;
pub mod eval;
pub mod frame;
pub mod map_arena;
pub mod pattern;
pub mod requirement_arena;
pub mod stream;
pub mod subst_arena;
pub mod value;

use std::collections::HashMap;

use crate::intern::Symbol;
use crate::kb::KnowledgeBase;
use crate::persistence::Store;

pub use error::EvalError;
pub use eval::value_functor;
pub use frame::{ActivationStack, Frame, FrameTypeArgs};
pub use value::Value;

use cell_arena::CellArenaRef;
use closure::ClosureArenaRef;
use effects::EffectRegistry;
use map_arena::MapArenaRef;
use requirement_arena::RequirementArenaRef;
use stream::StreamArenaRef;

/// Runtime resource limits. Each cap is optional so different embeddings
/// can trade safety against throughput independently.
///
/// - `depth_cap` bounds the activation stack. Non-tail recursion needs
///   O(n) frames and will trip this; tail recursion (TCO) stays O(1) and
///   is unaffected.
/// - `step_cap` bounds total interpreter work — one tick per `run()` trampoline
///   iteration, covering BOTH a `step()` reduction AND a value delivery. TCO
///   turns `loop() = loop()` into a constant-depth infinite loop that
///   `depth_cap` can't catch; likewise a dispatch/deliver value-cascade that
///   re-dispatches forever (a mis-resolved spec op) stays at constant
///   activation depth — both iterate on the trampoline, so each costs one step
///   and `step_cap` is the single guard that bounds them. On exhaustion the
///   `StepsExhausted` error carries the recent-dispatch ring, naming the
///   looping operations. Off by default so ordinary batch evaluation isn't
///   capped; the CLI binaries opt into a backstop cap (see `anthill::runner`).
#[derive(Clone, Copy, Debug)]
pub struct EvalConfig {
    pub depth_cap: Option<usize>,
    pub step_cap: Option<u64>,
    /// WI-625 gap 1 (SLD→eval bridge): this interpreter was lent to the resolver
    /// to run a host-bodied op at resolution. Because the resolver above CAN
    /// residualize (delay), a semantic comparison that reaches a genuinely
    /// undecided point must SUSPEND (`EvalError::Suspended`) rather than force a
    /// possibly-membership-wrong structural verdict — the resolver then delays.
    /// Off for every top-level eval (which has nowhere to suspend *to*, so its
    /// structural fallback is the documented behaviour).
    pub bridge_mode: bool,
}

impl Default for EvalConfig {
    fn default() -> Self {
        Self {
            depth_cap: Some(1_000_000),
            step_cap: None,
            bridge_mode: false,
        }
    }
}

impl EvalConfig {
    pub fn unbounded() -> Self {
        Self { depth_cap: None, step_cap: None, bridge_mode: false }
    }
}

/// Rust-side builtin: takes the interpreter and evaluated arg `Value`s,
/// returns a `Value` or an error. Mirrors `kb::resolve::builtins` in shape.
pub type BuiltinFn =
    std::sync::Arc<dyn Fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>>;

/// Proposal 039 / WI-084 — a term-level constant's memoized value state in
/// `Interpreter::const_cache`. `Forcing` marks a const whose value source is
/// currently being evaluated; re-entering it is a dependency cycle.
#[derive(Clone)]
pub(crate) enum ConstCacheEntry {
    /// The value is being computed right now — the dynamic cycle sentinel.
    Forcing,
    /// The forced value, shared by every later reference.
    Cached(Value),
}

/// Cached `Symbol`s for the reflect expression / pattern entities. Populated
/// at `Interpreter::new` via `kb.try_resolve_symbol`. An entry stays `None`
/// when the corresponding stdlib entity hasn't been loaded — the evaluator
/// surfaces a clear "unhandled functor" error instead of misbehaving.
///
/// Post-WI-248: most expression-form fields are no longer read by the
/// eval (NodeOccurrence dispatch is structural on the `Expr` variant,
/// not symbol-keyed). The fields remain populated for backwards-
/// compat and for any future passes that want a stable handle on the
/// canonical reflect entities — `#[allow(dead_code)]` lets the build
/// stay warning-clean. Pattern entities and collection literals are
/// still read directly (pattern matching and Value construction).
#[derive(Default, Debug)]
#[allow(dead_code)]
pub(crate) struct ReflectSymbols {
    // Expression entities
    pub int_lit: Option<Symbol>,
    pub float_lit: Option<Symbol>,
    pub bigint_lit: Option<Symbol>,
    pub string_lit: Option<Symbol>,
    pub bool_lit: Option<Symbol>,
    pub var_ref: Option<Symbol>,
    pub apply: Option<Symbol>,
    pub if_expr: Option<Symbol>,
    pub let_expr: Option<Symbol>,
    pub match_expr: Option<Symbol>,
    pub lambda: Option<Symbol>,
    pub constructor: Option<Symbol>,
    pub apply_within: Option<Symbol>,
    pub ho_apply_within: Option<Symbol>,
    pub constructor_within: Option<Symbol>,
    pub lambda_within: Option<Symbol>,
    pub requirement_at_sort: Option<Symbol>,
    pub construct_requirement: Option<Symbol>,

    // Pattern entities — still consulted by `eval::pattern::match_pattern`.
    pub var_pattern: Option<Symbol>,
    pub wildcard: Option<Symbol>,
    pub literal_pattern: Option<Symbol>,
    pub constructor_pattern: Option<Symbol>,
    pub tuple_pattern: Option<Symbol>,

    // Collection / list constructors — still consulted by Value
    // construction in `finish_constructor` / `build_list_value`.
    pub list_literal: Option<Symbol>,
    pub tuple_literal: Option<Symbol>,
    pub set_literal: Option<Symbol>,
    pub cons: Option<Symbol>,
    pub nil: Option<Symbol>,
    // WI-531: reflect `Solution` variants — the element shape `KB.execute`
    // streams now yield (`definite(subst)` / `undecided(subst, residual)`).
    pub solution_definite: Option<Symbol>,
    pub solution_undecided: Option<Symbol>,
}

impl ReflectSymbols {
    fn resolve(kb: &KnowledgeBase) -> Self {
        let r = |qn: &str| kb.try_resolve_symbol(qn);
        Self {
            int_lit: r("anthill.reflect.Expr.int_lit"),
            float_lit: r("anthill.reflect.Expr.float_lit"),
            bigint_lit: r("anthill.reflect.Expr.bigint_lit"),
            string_lit: r("anthill.reflect.Expr.string_lit"),
            bool_lit: r("anthill.reflect.Expr.bool_lit"),
            var_ref: r("anthill.reflect.Expr.var_ref"),
            apply: r("anthill.reflect.Expr.apply"),
            if_expr: r("anthill.reflect.Expr.if_expr"),
            let_expr: r("anthill.reflect.Expr.let_expr"),
            match_expr: r("anthill.reflect.Expr.match_expr"),
            lambda: r("anthill.reflect.Expr.lambda_expr"),
            constructor: r("anthill.reflect.Expr.constructor"),
            apply_within: r("anthill.reflect.Expr.apply_within"),
            ho_apply_within: r("anthill.reflect.Expr.ho_apply_within"),
            constructor_within: r("anthill.reflect.Expr.constructor_within"),
            lambda_within: r("anthill.reflect.Expr.lambda_within"),
            requirement_at_sort: r("anthill.reflect.Expr.requirement_at_sort"),
            construct_requirement: r("anthill.reflect.Expr.construct_requirement"),

            var_pattern: r("anthill.reflect.Pattern.var_pattern"),
            wildcard: r("anthill.reflect.Pattern.wildcard"),
            literal_pattern: r("anthill.reflect.Pattern.literal_pattern"),
            constructor_pattern: r("anthill.reflect.Pattern.constructor_pattern"),
            tuple_pattern: r("anthill.reflect.Pattern.tuple_pattern"),

            list_literal: r("anthill.reflect.ListLiteral"),
            tuple_literal: r("anthill.reflect.TupleLiteral"),
            set_literal: r("anthill.reflect.SetLiteral"),
            cons: r("anthill.prelude.List.cons"),
            nil: r("anthill.prelude.List.nil"),
            solution_definite: r("anthill.reflect.Solution.definite"),
            solution_undecided: r("anthill.reflect.Solution.undecided"),
        }
    }
}

/// Cached `Symbol`s for common named-arg field keys. Resolved once at
/// `Interpreter::new` via `kb.intern` so per-step lookups compare `Symbol`s
/// instead of scanning strings.
#[derive(Debug)]
#[allow(dead_code)]  // params/type_name/guard are reserved for future arms
pub(crate) struct FieldSymbols {
    pub value: Symbol,
    pub name: Symbol,
    pub cond: Symbol,
    pub then_branch: Symbol,
    pub else_branch: Symbol,
    pub pattern: Symbol,
    pub body: Symbol,
    pub fn_: Symbol,
    pub args: Symbol,
    /// WI-445: `constructor_pattern.named` — the `List[NamedPattern]` of
    /// `Foo(field: pat)` named sub-patterns.
    pub named: Symbol,
    pub params: Symbol,
    pub type_name: Symbol,
    pub scrutinee: Symbol,
    pub branches: Symbol,
    pub guard: Symbol,
    pub elements: Symbol,
    pub param: Symbol,
    pub head: Symbol,
    pub tail: Symbol,
    // WI-531 — reflect `Solution` field keys.
    pub subst: Symbol,
    pub residual: Symbol,
    // WI-222 / WI-223 — requirement IR field keys.
    pub slot: Symbol,
    pub op: Symbol,
    pub chain: Symbol,
    pub impl_functor: Symbol,
    pub requirements: Symbol,
    pub predicate: Symbol,
    /// `__req_self` — the Self-slot requirement-param name (WI-237
    /// names model). Interned, not a stdlib symbol.
    pub req_self: Symbol,
}

impl FieldSymbols {
    fn resolve(kb: &mut KnowledgeBase) -> Self {
        Self {
            value: kb.intern("value"),
            name: kb.intern("name"),
            cond: kb.intern("cond"),
            then_branch: kb.intern("then_branch"),
            else_branch: kb.intern("else_branch"),
            pattern: kb.intern("pattern"),
            body: kb.intern("body"),
            fn_: kb.intern("fn"),
            args: kb.intern("args"),
            named: kb.intern("named"),
            params: kb.intern("params"),
            type_name: kb.intern("type_name"),
            scrutinee: kb.intern("scrutinee"),
            branches: kb.intern("branches"),
            guard: kb.intern("guard"),
            elements: kb.intern("elements"),
            param: kb.intern("param"),
            head: kb.intern("head"),
            tail: kb.intern("tail"),
            subst: kb.intern("subst"),
            residual: kb.intern("residual"),
            slot: kb.intern("slot"),
            op: kb.intern("op"),
            chain: kb.intern("chain"),
            impl_functor: kb.intern("impl_functor"),
            requirements: kb.intern("requirements"),
            predicate: kb.intern("predicate"),
            req_self: kb.intern("__req_self"),
        }
    }
}

/// Top-level interpreter state. Owns the KB so builtins and effect handlers
/// can mutate it; host code takes it back via `Interpreter::into_kb()` when
/// evaluation is done.
pub struct Interpreter {
    pub(crate) kb: KnowledgeBase,
    pub(crate) stack: ActivationStack,
    pub(crate) builtins: HashMap<Symbol, BuiltinFn>,
    pub(crate) reflect: ReflectSymbols,
    pub(crate) fields: FieldSymbols,
    pub(crate) closures: ClosureArenaRef,
    pub(crate) streams: StreamArenaRef,
    pub(crate) substs: subst_arena::SubstArenaRef,
    pub(crate) maps: MapArenaRef,
    pub(crate) cells: CellArenaRef,
    pub(crate) requirements: RequirementArenaRef,
    pub(crate) effect_handlers: EffectRegistry,
    /// Registered persistence backends (proposal 007). Keyed by the
    /// canonical printed form of the store's `Value::Entity` so anthill
    /// code referencing the same shape (e.g. `FileStore(root: "x",
    /// convention: Flat)`) routes to the same instance across calls.
    /// The shim populates this before invoking `main` (see
    /// `Self::register_store`); persistence builtins look entries up.
    pub(crate) store_registry: HashMap<String, Box<dyn Store>>,
    /// Per-functor write policy provided by registered stores (proposal 053 /
    /// 007 §2), keyed by the functor's QUALIFIED NAME. Materialized at
    /// `register_store` from each store's `Store::owned_monotonicity`. The
    /// `fact_monotonicity` guard consults this as the fallback when no
    /// in-memory reflect rule fired — so a functor owned by an external store
    /// resolves to that store's policy, not the in-memory `monotone` default.
    /// String-keyed (not `Symbol`) so a store can name a functor whose symbol
    /// is interned later; the guard resolves against `qualified_name_of`.
    pub(crate) store_monotonicity: HashMap<String, crate::persistence::Monotonicity>,
    /// Memoized operation-body lookups. `lookup_operation_body` linear-scans
    /// every `OperationInfo` fact to find the one matching the op symbol, so
    /// without this cache every operation call is O(num_operations) — which
    /// dominates interpreted runtime once a program makes many calls. The
    /// `OperationInfo` facts are static across a run (only data facts get
    /// persisted/retracted), so memoizing by op `Symbol` is sound.
    pub(crate) op_body_cache: HashMap<Symbol, eval::OpBody>,
    /// Proposal 039 / WI-084 — memoized term-level-constant values, keyed by the
    /// const's `SymbolKind::Const` symbol. THE memoization the proposal calls for:
    /// a const's value source is forced AT MOST ONCE and shared by every
    /// reference (referentially transparent — the source is pure). The `Forcing`
    /// sentinel is the dynamic cycle detector: re-demanding a const already being
    /// forced is `ConstCycle`, not an infinite fold. Distinct from
    /// `op_body_cache` (which caches body *lookups*, not values).
    pub(crate) const_cache: HashMap<Symbol, ConstCacheEntry>,
    /// Whether the `ANTHILL_PROFILE` profiler is active. Read once from the
    /// environment at construction (it can't change mid-run) so the per-step
    /// and per-dispatch profiling gates are a plain field test, not an env
    /// lookup. See `eval::OP_PROF` / `Self::dump_profile`.
    pub(crate) profiling: bool,
    pub(crate) config: EvalConfig,
    /// Monotonically increasing step counter, reset on each `call()`.
    /// `run()` increments it once per `step()` and compares against
    /// `config.step_cap`. Not a permanent counter — after a call returns
    /// the host can inspect and reset via `config_mut()`.
    pub(crate) step_count: u64,
    /// Bounded ring of the most recent dispatch targets (newest at the back),
    /// reset per top-level call. Maintained only when a `step_cap` is set (its
    /// sole reader is `StepsExhausted`, which can only fire under a cap); on
    /// that error its contents name the looping operations (a loop repeats its
    /// ops, so they fill the ring).
    pub(crate) recent_dispatches: std::collections::VecDeque<Symbol>,
}

/// Collect the top-`n` profiler entries from a thread-local counter map,
/// sorted descending by the second field (reductions or wall nanos), and
/// clear the map for the next run. Shared by `dump_profile`'s op + builtin
/// tables. See `eval::OP_PROF` / `eval::BUILTIN_PROF`.
fn drain_top<V: Copy + Ord>(
    prof: &'static std::thread::LocalKey<std::cell::RefCell<HashMap<Symbol, (u64, V)>>>,
    n: usize,
) -> Vec<(Symbol, (u64, V))> {
    prof.with(|p| {
        let mut rows: Vec<(Symbol, (u64, V))> =
            p.borrow().iter().map(|(k, v)| (*k, *v)).collect();
        rows.sort_by(|a, b| b.1 .1.cmp(&a.1 .1));
        rows.truncate(n);
        p.borrow_mut().clear();
        rows
    })
}

impl Interpreter {
    pub fn new(kb: KnowledgeBase) -> Self {
        Self::with_config(kb, EvalConfig::default())
    }

    pub fn with_config(mut kb: KnowledgeBase, config: EvalConfig) -> Self {
        let reflect = ReflectSymbols::resolve(&kb);
        let fields = FieldSymbols::resolve(&mut kb);
        let stack = match config.depth_cap {
            Some(cap) => ActivationStack::with_cap(cap),
            None => ActivationStack::with_cap(usize::MAX),
        };
        Self {
            kb,
            stack,
            builtins: HashMap::new(),
            reflect,
            fields,
            closures: ClosureArenaRef::new(),
            streams: StreamArenaRef::new(),
            substs: subst_arena::SubstArenaRef::new(),
            maps: MapArenaRef::new(),
            cells: CellArenaRef::new(),
            requirements: RequirementArenaRef::new(),
            effect_handlers: EffectRegistry::new(),
            store_registry: HashMap::new(),
            store_monotonicity: HashMap::new(),
            op_body_cache: HashMap::new(),
            const_cache: HashMap::new(),
            profiling: std::env::var_os("ANTHILL_PROFILE").is_some(),
            config,
            step_count: 0,
            recent_dispatches: std::collections::VecDeque::new(),
        }
    }

    pub fn config(&self) -> &EvalConfig { &self.config }

    pub fn config_mut(&mut self) -> &mut EvalConfig { &mut self.config }

    pub fn kb(&self) -> &KnowledgeBase { &self.kb }
    pub fn kb_mut(&mut self) -> &mut KnowledgeBase { &mut self.kb }
    pub fn into_kb(self) -> KnowledgeBase { self.kb }

    /// Number of live closure-arena slots. Exposed so refcount/GC tests can
    /// assert reclamation after evaluation (see WI-055, WI-058). Useful
    /// diagnostic at runtime too.
    pub fn closure_arena_live_count(&self) -> usize { self.closures.live() }

    /// Register a Rust builtin keyed by the fully-qualified operation name.
    /// Returns `Err` if the name can't be resolved in the KB's symbol table.
    pub fn register_builtin<F>(&mut self, qualified_name: &str, f: F) -> Result<(), EvalError>
    where
        F: Fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError> + 'static,
    {
        let sym = self.kb.try_resolve_symbol(qualified_name).ok_or_else(|| {
            EvalError::UnknownOperation { name: qualified_name.to_string() }
        })?;
        self.builtins.insert(sym, std::sync::Arc::new(f));
        Ok(())
    }

    /// Register a persistence backend, keyed by its canonical store-value
    /// form. Anthill code that calls `persist`/`retract`/`flush` with a
    /// `Value::Entity` whose canonical form matches `key` routes to this
    /// instance. Replaces any prior registration under the same key.
    /// Use [`Self::store_canonical_key`] to compute the key from the
    /// store's value representation.
    ///
    /// Materializes the store's per-functor write policy (proposal 053 /
    /// 007 §2) into `store_monotonicity` so the `fact_monotonicity` guard can
    /// resolve an externally-owned functor to its owning store's answer.
    pub fn register_store(&mut self, key: String, store: Box<dyn Store>) {
        for (functor_name, mono) in store.owned_monotonicity() {
            self.store_monotonicity.insert(functor_name, mono);
        }
        self.store_registry.insert(key, store);
    }

    /// Compute the canonical-key string for a store value (`Value::Entity`).
    /// Same string for any two values that compare equal under
    /// `views_structurally_equal` modulo named-arg ordering.
    pub fn store_canonical_key(&self, v: &Value) -> Result<String, EvalError> {
        let mut buf = String::new();
        self.write_value_canonical(v, &mut buf)?;
        Ok(buf)
    }

    /// Recursive helper for [`Self::store_canonical_key`].
    fn write_value_canonical(&self, v: &Value, buf: &mut String) -> Result<(), EvalError> {
        match v {
            Value::Int(n) => buf.push_str(&n.to_string()),
            Value::BigInt(n) => buf.push_str(&n.to_string()),
            Value::Float(f) => {
                let s = f.to_string();
                buf.push_str(&s);
                if !s.contains('.') { buf.push_str(".0"); }
            }
            Value::Bool(b) => buf.push_str(if *b { "true" } else { "false" }),
            Value::Str(s) => crate::persistence::print::write_anthill_string(s, buf),
            Value::Entity { functor, pos, named, .. } => {
                buf.push_str(self.kb.resolve_sym(*functor));
                if pos.is_empty() && named.is_empty() {
                    return Ok(());
                }
                buf.push('(');
                let mut first = true;
                for p in pos.iter() {
                    if !first { buf.push_str(", "); }
                    first = false;
                    self.write_value_canonical(p, buf)?;
                }
                let mut sorted: Vec<&(Symbol, Value)> = named.iter().collect();
                sorted.sort_by(|a, b| {
                    self.kb.resolve_sym(a.0).cmp(self.kb.resolve_sym(b.0))
                });
                for (sym, val) in sorted {
                    if !first { buf.push_str(", "); }
                    first = false;
                    buf.push_str(self.kb.resolve_sym(*sym));
                    buf.push_str(": ");
                    self.write_value_canonical(val, buf)?;
                }
                buf.push(')');
            }
            Value::Term { id: tid, .. } => {
                buf.push_str(&crate::persistence::print::TermPrinter::new(&self.kb).print_term(*tid));
            }
            Value::Unit
            | Value::Tuple { .. }
            | Value::Closure(_)
            | Value::OpRef { .. }
            | Value::Stream(_)
            | Value::Substitution(_)
            | Value::Map(_)
            | Value::Cell(_)
            | Value::Requirement(_)
            | Value::Node(_)
            // WI-714: a `Relation` is a query value, never persisted store data.
            | Value::Relation { .. }
            // WI-109: an unbound logic variable has no canonical store key.
            | Value::Var(_) => {
                return Err(EvalError::TypeMismatch {
                    expected: "store-shaped Value (Entity / scalar / Term)",
                    got: v.type_name().to_string(),
                });
            }
        }
        Ok(())
    }

    /// Invoke an anthill operation by qualified name with the given argument
    /// values. The operation is looked up via `OperationInfo` facts — the
    /// stdlib + user code must already be loaded. If the operation is
    /// backed by a registered Rust builtin (no anthill body), the builtin
    /// runs directly without a frame push.
    ///
    /// Requirements (dictionary values for the parent sort's `requires`
    /// chain) are auto-seeded as self-referential placeholders: each slot
    /// is a `Requirement { functor: parent_sort, requirements: [] }`. That
    /// shape covers same-sort recursion (the dominant CLI entry case) but
    /// not cross-sort dispatch — when the parent sort's `requires` names a
    /// different sort (e.g. `requires WorkItemStore[State]`), the
    /// placeholder won't reach the named impl and the body will surface a
    /// dispatch/slot mismatch at runtime. Use
    /// [`Self::call_with_requirements`] to supply real impl-rooted
    /// dictionaries from the host. See `docs/design/operation-call-model.md`
    /// §"Host-to-entry-op boundary".
    pub fn call(&mut self, qualified_name: &str, args: &[Value]) -> Result<Value, EvalError> {
        let sym = self.kb.try_resolve_symbol(qualified_name).ok_or_else(|| {
            EvalError::UnknownOperation { name: qualified_name.to_string() }
        })?;
        self.call_op_sym(sym, args)
    }

    /// Symbol-keyed body of [`Self::call`]: dispatch to a registered builtin,
    /// else seed the entry op's `requires` chain with self-referential
    /// placeholders and invoke it. Private — host callers use `call` (by name);
    /// the resolver bridge uses [`Self::call_op_bridged`] (which does NOT seed
    /// placeholders — see there for why).
    fn call_op_sym(&mut self, sym: Symbol, args: &[Value]) -> Result<Value, EvalError> {
        if let Some(builtin) = self.builtins.get(&sym).cloned() {
            return (builtin)(self, args);
        }
        let requirements = self.seed_entry_requirements(sym);
        self.invoke_op_with_requirements(sym, args, requirements)
    }

    /// WI-625 gap 1 + Layer B: the resolver→eval bridge entry
    /// ([`crate::kb::KnowledgeBase::bridge_op_to_eval`]). Like [`Self::call`] but
    /// invoked BY SYMBOL (the resolver holds it already).
    ///
    /// The requirement dictionaries are RESOLVED at the concrete argument types
    /// ([`crate::kb::typing::resolve_bridge_requirements`], WI-300 Tier B / gap 3),
    /// NOT seeded with [`Self::seed_entry_requirements`]'s self-referential
    /// placeholders — a placeholder can misdispatch a `requires` op to a
    /// wrong-but-non-erroring impl and return a plausibly-WRONG value, which the
    /// resolver would import as a definite `eq`/`cmp` answer (an unsoundness the
    /// pre-bridge delay never had). Instead:
    ///   * a requirement-FREE op runs with empty dicts (the gap-1 behavior);
    ///   * a requires-carrying op gets REAL provider dicts, so its body's spec-op
    ///     dispatch reaches the right impl and DECIDES (the gap-3 win);
    ///   * a requirement that cannot be resolved uniquely at these arg types
    ///     ([`BridgeRequirements::Unresolvable`]) SUSPENDS → the bridge residualizes,
    ///     never running with a wrong or missing dict.
    pub(crate) fn call_op_bridged(&mut self, sym: Symbol, args: &[Value]) -> Result<Value, EvalError> {
        if let Some(builtin) = self.builtins.get(&sym).cloned() {
            return (builtin)(self, args);
        }
        use crate::kb::typing::BridgeRequirements;
        let requirements = match crate::kb::typing::resolve_bridge_requirements(&mut self.kb, sym, args) {
            BridgeRequirements::NoneNeeded => smallvec::SmallVec::new(),
            BridgeRequirements::Unresolvable => {
                return Err(EvalError::Suspended {
                    detail: format!(
                        "bridge: cannot resolve a required dictionary for `{}` at these argument types",
                        self.kb.qualified_name_of(sym),
                    ),
                    // A missing dictionary is a flounder, not a truncated search.
                    truncated: false,
                });
            }
            BridgeRequirements::Resolved(parent, trees) => {
                let mut out: smallvec::SmallVec<[(Symbol, value::RequirementHandle); 2]> =
                    smallvec::SmallVec::with_capacity(trees.len() + 1);
                // Slot 0 = Self placeholder (the op's own parent sort), then one
                // real provider handle per `requires` slot — the same layout
                // `call_with_requirements` assembles for a host caller.
                out.push((self.fields.req_self, self.requirements.alloc(parent, smallvec::SmallVec::new())));
                for (name, tree) in &trees {
                    match self.port_resolved_tree(tree) {
                        Some(handle) => out.push((*name, handle)),
                        None => {
                            return Err(EvalError::Suspended {
                                detail: format!(
                                    "bridge: requirement for `{}` resolved to a caller-scope slot with no caller frame",
                                    self.kb.qualified_name_of(sym),
                                ),
                                // A missing caller frame is a flounder, not truncation.
                                truncated: false,
                            });
                        }
                    }
                }
                out
            }
        };
        self.invoke_op_with_requirements(sym, args, requirements)
    }

    /// WI-625 Layer B: port a resolved requirement tree
    /// ([`crate::kb::typing::ResolvedRequiresNode`]) to a runtime
    /// [`value::RequirementHandle`] — the runtime dual of the typer's
    /// `emit_tree_as_projection`. A `Leaf` allocates a handle over its impl carrier
    /// with no sub-requirements; a `Conditional` recurses each sub-resolution into a
    /// nested handle first (so `handle.arity()` matches the impl's own `requires`
    /// chain, satisfying the eval dispatcher's cross-check). `FromScope` cannot arise
    /// here (the bridge resolves with an empty scope) — returns `None` (residualize)
    /// if it somehow does.
    fn port_resolved_tree(
        &self,
        tree: &crate::kb::typing::ResolvedRequiresNode,
    ) -> Option<value::RequirementHandle> {
        use crate::kb::typing::ResolvedRequiresNode;
        match tree {
            ResolvedRequiresNode::Leaf { impl_sort, .. } => {
                Some(self.requirements.alloc(*impl_sort, smallvec::SmallVec::new()))
            }
            ResolvedRequiresNode::Conditional { impl_sort, sub_resolutions, .. } => {
                let mut subs: smallvec::SmallVec<[value::RequirementHandle; 1]> =
                    smallvec::SmallVec::with_capacity(sub_resolutions.len());
                for sub in sub_resolutions {
                    subs.push(self.port_resolved_tree(sub)?);
                }
                Some(self.requirements.alloc(*impl_sort, subs))
            }
            ResolvedRequiresNode::FromScope { .. } => None,
        }
    }

    /// WI-625 gap 1: is this interpreter running as the resolver's op-body
    /// bridge? When set, semantic comparisons that reach an undecided point
    /// suspend ([`EvalError::Suspended`]) instead of forcing a structural
    /// verdict. See [`EvalConfig::bridge_mode`].
    pub(crate) fn bridge_mode(&self) -> bool {
        self.config.bridge_mode
    }

    /// WI-625 gap 1: materialize a term-carried value into the interpreter's
    /// NATIVE form — a `Value::Term(Ref/Fn ctor)` becomes a `Value::Entity`
    /// (recursively), literals become scalars. The resolver hands the bridge its
    /// operands as term carriers (`Value::Term`), but eval builtins like
    /// `field_access` require a real `Value::Entity`; without this a bridged body
    /// that reads a field errors with "receiver is not an entity (got Term)".
    /// A non-term value (already native) passes through.
    ///
    /// WI-685: a `Value::Node` occurrence operand (a rule-body `eq`/`neq` operand,
    /// which the resolver no longer collapses to a `Value::Term` before the bridge)
    /// is lowered the same way — to a term, then to the native form — so a bridged
    /// body reads a real `Value::Entity`, not an occurrence.
    pub(crate) fn materialize_value(&mut self, v: Value) -> Value {
        match v {
            Value::Term { id, .. } => builtins::term_to_value(self, id),
            Value::Node(occ) => {
                let tid = crate::kb::node_occurrence::occurrence_to_term(&mut self.kb, &occ);
                builtins::term_to_value(self, tid)
            }
            other => other,
        }
    }

    /// Variant of [`Self::call`] that lets the host supply real
    /// impl-rooted dictionaries for the entry op's `requires` chain,
    /// instead of [`Self::seed_entry_requirements`]'s self-referential
    /// placeholders.
    ///
    /// `chain_dicts` is one handle per entry in the parent sort's
    /// flattened `requires` chain (in declaration order). The frame's
    /// Self slot (slot 0) is auto-allocated by this method as a
    /// self-referential placeholder for the parent sort — host callers
    /// don't see it. The supplied handles populate slots 1..=N.
    ///
    /// Required when the parent sort declares `requires X[…]` for a
    /// different sort X (e.g. `sort Main { requires
    /// WorkItemStore[State] }`): plain [`Self::call`] would seed slot 1
    /// with `Requirement{ functor: Main, … }`, and body-side
    /// `WorkItemStore.lookup(…)` would dispatch through the placeholder
    /// — wrong impl, runtime mis-dispatch.
    ///
    /// Use [`Self::alloc_requirement`] to build each handle. See
    /// `docs/design/operation-call-model.md` §"Host-to-entry-op boundary".
    pub fn call_with_requirements(
        &mut self,
        qualified_name: &str,
        args: &[Value],
        chain_dicts: smallvec::SmallVec<[value::RequirementHandle; 2]>,
    ) -> Result<Value, EvalError> {
        let sym = self.kb.try_resolve_symbol(qualified_name).ok_or_else(|| {
            EvalError::UnknownOperation { name: qualified_name.to_string() }
        })?;
        if let Some(builtin) = self.builtins.get(&sym).cloned() {
            return (builtin)(self, args);
        }
        // Names model: `__req_self` → a self-referential placeholder for
        // the parent sort; `__req_<spec>` → each host-supplied chain
        // dict, zipped against `synth_req_names`. The arity check uses
        // the same name list as the bind step so the two can't diverge
        // (a prior version used `requires_chain_flat` here, which can
        // see different cache state than `synth_req_names`'s
        // substitution-composed walk). See operation-call-model.md
        // §"Host-to-entry-op boundary".
        let parent_sym = crate::kb::typing::impl_parent_of_op(&self.kb, sym);
        let names = parent_sym
            .map(|p| crate::kb::typing::synth_req_names(&mut self.kb, p));
        let expected = names.as_ref().map_or(0, |n| n.len());
        if chain_dicts.len() != expected {
            return Err(EvalError::Internal(format!(
                "call_with_requirements({qualified_name}): expected {expected} \
                 requirement slot(s) (the parent sort's requires chain), got {got}",
                got = chain_dicts.len(),
            )));
        }
        let mut requirements: smallvec::SmallVec<[(Symbol, value::RequirementHandle); 2]> =
            smallvec::SmallVec::new();
        if let (Some(p), Some(names)) = (parent_sym, names) {
            let placeholder = self.requirements.alloc(p, smallvec::SmallVec::new());
            requirements.push((self.fields.req_self, placeholder));
            for (name, dict) in names.iter().zip(chain_dicts) {
                requirements.push((*name, dict));
            }
        }
        self.invoke_op_with_requirements(sym, args, requirements)
    }

    /// Shared body of [`Self::call`] and [`Self::call_with_requirements`]:
    /// validate arity, build the frame's locals, push, run.
    fn invoke_op_with_requirements(
        &mut self,
        sym: Symbol,
        args: &[Value],
        requirements: smallvec::SmallVec<[(Symbol, value::RequirementHandle); 2]>,
    ) -> Result<Value, EvalError> {
        let (body_term, params) = match self.cached_operation_body(sym) {
            Some(b) => b,
            // WI-625 (eval→SLD bridge): a host-invoked body-less carrier `eq` op
            // (e.g. `Set.eq`/`Map.eq` resolved from a dictionary — gap 4) has no
            // body to run, but the SLD resolver can prove it. The host-entry twin
            // of the in-body dispatch bridge; anything else stays a loud
            // `OperationBodyMissing`.
            None => match self.eq_bridge_target(sym, args) {
                Some(pred) => return self.prove_rule_predicate_value(pred, args),
                None => {
                    return Err(EvalError::OperationBodyMissing {
                        name: self.kb.qualified_name_of(sym).to_string(),
                        backtrace: std::backtrace::Backtrace::force_capture(),
                    });
                }
            },
        };
        if args.len() != params.len() {
            return Err(EvalError::ArityMismatch {
                op: "operation call",
                expected: params.len(),
                got: args.len(),
            });
        }
        let mut locals: smallvec::SmallVec<[(Symbol, Value); 4]> = smallvec::SmallVec::new();
        for (i, (pname, _)) in params.iter().enumerate() {
            locals.push((*pname, args[i].clone()));
        }
        self.step_count = 0;
        self.recent_dispatches.clear();
        self.stack.push(Frame {
            op: sym,
            expr: body_term,
            locals,
            requirements,
            type_args: smallvec::SmallVec::new(),
            awaiting: None,
        })?;
        let result = self.run();
        if self.profiling {
            self.dump_profile(sym);
        }
        result
    }

    /// Dump the exact operation/builtin profile collected during the last
    /// top-level run (env `ANTHILL_PROFILE`). Clears the counters so a
    /// subsequent top-level call starts fresh.
    fn dump_profile(&self, entry: Symbol) {
        eprintln!(
            "[profile] entry={} total-reductions={}",
            self.kb.qualified_name_of(entry),
            self.step_count,
        );
        eprintln!("[profile] top operations (by self-reductions):");
        for (sym, (calls, steps)) in drain_top(&eval::OP_PROF, 20) {
            eprintln!(
                "[profile]   {:<46} self-reductions={:<9} calls={}",
                self.kb.qualified_name_of(sym), steps, calls,
            );
        }
        eprintln!("[profile] top builtins (by wall time):");
        for (sym, (calls, nanos)) in drain_top(&eval::BUILTIN_PROF, 15) {
            eprintln!(
                "[profile]   {:<46} {:>8.3}ms  calls={}",
                self.kb.qualified_name_of(sym),
                nanos as f64 / 1.0e6, calls,
            );
        }
    }

    /// Build the initial `frame.requirements` for an entry-point call.
    /// Per WI-234 / Model 1 the layout is: slot 0 = Self (the entry op's
    /// parent sort), slots 1..=N = one per entry in the parent's flattened
    /// `requires` chain. Both Self and chain entries are self-referential
    /// placeholders (`functor = parent_sort, sub_requires = []`) — adequate
    /// for same-sort recursion but mis-dispatches when the parent's
    /// `requires` clause names a different sort. Cross-sort entries
    /// should use [`Self::call_with_requirements`].
    fn seed_entry_requirements(
        &mut self,
        op_sym: Symbol,
    ) -> smallvec::SmallVec<[(Symbol, value::RequirementHandle); 2]> {
        let Some(parent_sym) = crate::kb::typing::impl_parent_of_op(&self.kb, op_sym) else {
            return smallvec::SmallVec::new();
        };
        let names = crate::kb::typing::synth_req_names(&mut self.kb, parent_sym);
        let mut out: smallvec::SmallVec<[(Symbol, value::RequirementHandle); 2]> =
            smallvec::SmallVec::with_capacity(names.len() + 1);
        out.push((
            self.fields.req_self,
            self.requirements.alloc(parent_sym, smallvec::SmallVec::new()),
        ));
        for name in names.iter() {
            out.push((
                *name,
                self.requirements.alloc(parent_sym, smallvec::SmallVec::new()),
            ));
        }
        out
    }

    /// Override the activation-stack depth cap. Kept as a convenience wrapper
    /// over `config_mut()` for tests that only care about the depth limit.
    pub fn set_stack_depth_cap(&mut self, cap: usize) {
        self.config.depth_cap = Some(cap);
        self.stack.set_cap(cap);
    }

    /// Number of live stream-arena slots. Diagnostic for refcount tests.
    pub fn stream_arena_live_count(&self) -> usize { self.streams.live() }

    /// Number of live substitution-arena slots. Diagnostic for refcount tests.
    pub fn subst_arena_live_count(&self) -> usize { self.substs.live() }

    /// Number of live map-arena slots. Diagnostic for refcount tests.
    pub fn map_arena_live_count(&self) -> usize { self.maps.live() }

    /// Allocate a fresh map slot and return a handle.
    pub fn alloc_map(&self, body: map_arena::MapBody) -> value::MapHandle {
        self.maps.alloc(body)
    }

    /// Run `f` with a shared reference to the map body behind `h`.
    pub fn with_map<R>(
        &self,
        h: &value::MapHandle,
        f: impl FnOnce(&map_arena::MapBody) -> R,
    ) -> R {
        self.maps.with_body(h, f)
    }

    /// Clone the map-arena handle. Same rationale as `subst_arena()`.
    pub fn map_arena(&self) -> MapArenaRef {
        self.maps.clone()
    }

    /// Number of live cell-arena slots. Diagnostic for refcount tests.
    pub fn cell_arena_live_count(&self) -> usize { self.cells.live() }

    /// Number of live requirement-arena slots. Diagnostic for refcount
    /// and cascade-drop tests under the WI-223 runtime support.
    pub fn requirement_arena_live_count(&self) -> usize { self.requirements.live() }

    /// Allocate a fresh requirement slot bundling `(functor, requirements)`
    /// and return an owning handle. Used by the eval to reduce
    /// `construct_requirement(impl, [...])` IR forms.
    pub fn alloc_requirement(
        &self,
        functor: Symbol,
        requirements: smallvec::SmallVec<[value::RequirementHandle; 1]>,
    ) -> value::RequirementHandle {
        self.requirements.alloc(functor, requirements)
    }

    /// Test-only: read a closure's snapshotted `requirements` channel.
    /// Used to verify that lambda construction captures the enclosing
    /// frame's requirements (acceptance #4 of WI-223).
    #[doc(hidden)]
    pub fn closure_requirements_for_test(
        &self,
        h: &value::ClosureHandle,
    ) -> smallvec::SmallVec<[(Symbol, value::RequirementHandle); 1]> {
        self.closures.with(h, |c| c.requirements.clone())
    }

    /// Test-only: snapshot the top frame's operation type-arg
    /// channel. Acceptance fixtures observe what the eval installed
    /// on `Frame.type_args` after a call entry (WI-272). Empty when
    /// the stack is empty or the top frame has no type params.
    #[doc(hidden)]
    pub fn top_frame_type_args_for_test(&self) -> FrameTypeArgs {
        self.stack.top()
            .map(|f| f.type_args.clone())
            .unwrap_or_default()
    }

    /// Test-only entry point: drive a single expression as the body of an
    /// ad-hoc operation, with `frame.requirements` pre-seeded. Used to
    /// verify the WI-223 requirement IR reductions
    /// (`requirement_at_current` / `requirement_at_sort` /
    /// `construct_requirement`) before WI-222's rewrite pass produces them
    /// from real call sites.
    #[doc(hidden)]
    pub fn run_with_requirements(
        &mut self,
        expr: crate::kb::term::TermId,
        requirements: smallvec::SmallVec<[(Symbol, value::RequirementHandle); 2]>,
    ) -> Result<Value, EvalError> {
        let op = self.kb.intern("__test_requirement_eval");
        self.step_count = 0;
        self.recent_dispatches.clear();
        // Test-entry materializes a NodeOccurrence from the test's
        // legacy Term::Fn input. The materializer handles both Handle-
        // wrapped trees (loader output) and naked Fn shapes (test
        // construction); see materialize_from_handle for the fallback.
        let expr_node = crate::kb::node_occurrence::materialize_from_handle(&self.kb, expr);
        self.stack.push(Frame {
            op,
            expr: expr_node,
            locals: smallvec::SmallVec::new(),
            requirements,
            type_args: smallvec::SmallVec::new(),
            awaiting: None,
        })?;
        self.run()
    }

    /// Clone the requirement-arena handle. Same rationale as
    /// `subst_arena()`: lets a caller hold a borrow on the arena while
    /// `&mut self` on the interpreter is in flight.
    pub fn requirement_arena(&self) -> RequirementArenaRef {
        self.requirements.clone()
    }

    /// Allocate a fresh cell slot and return an owning handle.
    pub fn alloc_cell(&self, value: Value) -> value::CellHandle {
        self.cells.alloc(value)
    }

    /// Snapshot the value held in `h`.
    pub fn read_cell(&self, h: &value::CellHandle) -> Value {
        self.cells.read(h)
    }

    /// Replace the value in `h`; returns the prior value.
    pub fn write_cell(&self, h: &value::CellHandle, new: Value) -> Value {
        self.cells.write(h, new)
    }

    /// Clone the cell-arena handle (cheap `Rc` bump). Same rationale as
    /// `subst_arena()`: lets a caller hold a borrow on the arena while
    /// `&mut self` on the interpreter is in flight.
    pub fn cell_arena(&self) -> CellArenaRef {
        self.cells.clone()
    }

    /// Allocate a fresh substitution slot and return a handle.
    pub fn alloc_subst(&self, s: crate::kb::subst::Substitution) -> value::SubstHandle {
        self.substs.alloc(s)
    }

    /// Run `f` with a shared reference to the substitution behind `h`.
    pub fn with_subst<R>(
        &self,
        h: &value::SubstHandle,
        f: impl FnOnce(&crate::kb::subst::Substitution) -> R,
    ) -> R {
        self.substs.with_subst(h, f)
    }

    /// Clone the substitution-arena handle. Useful when a caller needs to
    /// borrow a substitution through the arena while also mutably borrowing
    /// `kb`; both fields are independent, so the cloned `Rc` decouples the
    /// arena borrow from any `&mut self` on the interpreter.
    pub fn subst_arena(&self) -> subst_arena::SubstArenaRef {
        self.substs.clone()
    }

    /// Allocate a stream source, returning an owning handle.
    pub fn alloc_stream(&self, src: stream::StreamSource) -> value::StreamHandle {
        self.streams.alloc(src)
    }

    /// Pump a stream by one step. Returns `Some((value, continuation))` for
    /// a yielded element, or `None` on exhaustion. The continuation is a
    /// fresh handle sharing the underlying arena slot(s) — for `Resolver`
    /// it's the same slot advanced in place; for `MPlus` with `left`
    /// exhausted, it's the `right` child's handle.
    ///
    /// Resolver yields land as a reflect `Solution` value (WI-531) —
    /// `definite(subst)` or `undecided(subst, residual)` — built by
    /// [`Self::make_solution_value`]. `subst` is a `Value::Substitution`
    /// handle into the per-interpreter arena (read via `Substitution.lookup` /
    /// `.apply`); the floundered `undecided` case additionally carries the
    /// undischarged goals as a `List[Term]`, so the residual is no longer
    /// silently dropped here.
    pub fn stream_split_first(
        &mut self,
        handle: &value::StreamHandle,
    ) -> Result<Option<(Value, value::StreamHandle)>, EvalError> {
        use stream::StreamSource;
        enum Action {
            Done,
            YieldSelf(Value),
            PumpResolver(crate::kb::resolve::SearchStream),
            // WI-714: pump the resolver one step, then MATERIALIZE the yielded
            // Solution onto `columns` into a named-tuple row (see below).
            PumpMaterialized {
                search: crate::kb::resolve::SearchStream,
                columns: std::rc::Rc<[(crate::intern::Symbol, crate::kb::term::VarId)]>,
            },
            PumpLeft { left: value::StreamHandle, right: value::StreamHandle },
        }

        let arena = self.streams.clone();
        let action = arena.with_source_mut(handle, |src| match src {
            StreamSource::Empty => (StreamSource::Empty, Action::Done),
            StreamSource::Resolver(None) => (StreamSource::Resolver(None), Action::Done),
            StreamSource::Resolver(Some(stream)) => (
                StreamSource::Resolver(None),
                Action::PumpResolver(stream),
            ),
            // WI-714: a materializing resolver — same pump lifecycle as `Resolver`
            // (take the `SearchStream`, leave `None` transiently), but its yielded
            // element is the materialized named-tuple row, not the raw `Solution`.
            StreamSource::MaterializedResolver { search: None, columns } => (
                StreamSource::MaterializedResolver { search: None, columns },
                Action::Done,
            ),
            StreamSource::MaterializedResolver { search: Some(stream), columns } => (
                StreamSource::MaterializedResolver { search: None, columns: columns.clone() },
                Action::PumpMaterialized { search: stream, columns },
            ),
            StreamSource::Pure(mut slot) => match slot.take() {
                Some(v) => (StreamSource::Empty, Action::YieldSelf(v)),
                None => (StreamSource::Empty, Action::Done),
            },
            StreamSource::MPlus { left, right } => (
                StreamSource::MPlus { left: left.clone(), right: right.clone() },
                Action::PumpLeft { left, right },
            ),
            StreamSource::Native(mut f) => match f() {
                Some(v) => (StreamSource::Native(f), Action::YieldSelf(v)),
                None => (StreamSource::Empty, Action::Done),
            },
            StreamSource::External(mut s) => match s.next() {
                Some(v) => (StreamSource::External(s), Action::YieldSelf(v)),
                None => (StreamSource::Empty, Action::Done),
            },
        });

        match action {
            Action::Done => Ok(None),
            Action::YieldSelf(v) => Ok(Some((v, handle.clone()))),
            Action::PumpResolver(stream) => {
                let result = stream.split_first(&mut self.kb);
                let stream_arena = self.streams.clone();
                match result {
                    Some((sol, rest)) => {
                        stream_arena.with_source_mut(handle, |_| {
                            (StreamSource::Resolver(Some(rest)), ())
                        });
                        let solution = self.make_solution_value(sol)?;
                        Ok(Some((solution, handle.clone())))
                    }
                    None => {
                        stream_arena.with_source_mut(handle, |_| (StreamSource::Empty, ()));
                        Ok(None)
                    }
                }
            }
            Action::PumpMaterialized { search, columns } => {
                // WI-714: pump one resolver step, then materialize the answer onto
                // the relation's free variables (`columns`) — the one place a
                // relation solution becomes a value row.
                let result = search.split_first(&mut self.kb);
                let stream_arena = self.streams.clone();
                match result {
                    Some((sol, rest)) => {
                        let cols = columns.clone();
                        stream_arena.with_source_mut(handle, move |_| {
                            (StreamSource::MaterializedResolver { search: Some(rest), columns: cols }, ())
                        });
                        let row = self.materialize_solution(sol, &columns)?;
                        Ok(Some((row, handle.clone())))
                    }
                    None => {
                        stream_arena.with_source_mut(handle, |_| (StreamSource::Empty, ()));
                        Ok(None)
                    }
                }
            }
            Action::PumpLeft { left, right } => match self.stream_split_first(&left)? {
                Some((v, left_rest)) => {
                    let arena = self.streams.clone();
                    arena.with_source_mut(handle, |_| {
                        (StreamSource::MPlus { left: left_rest, right: right.clone() }, ())
                    });
                    Ok(Some((v, handle.clone())))
                }
                None => self.stream_split_first(&right),
            },
        }
    }

    /// WI-531: wrap a resolver [`Solution`](crate::kb::resolve::Solution) as a
    /// reflect `Solution` value. A *definite* solution (empty residual) becomes
    /// `definite(subst)`; a *floundered* one becomes `undecided(subst,
    /// residual)`, carrying its undischarged goals as a `List[Term]` so anthill
    /// consumers (the WI-010 self-hosted type resolver) can inspect WHICH goals
    /// stayed pending — keeping reflect a faithful description of the core.
    /// Undecidedness is a third logical outcome carried as DATA, never raised
    /// on `execute`'s `E = Error` channel.
    fn make_solution_value(
        &mut self,
        sol: crate::kb::resolve::Solution,
    ) -> Result<Value, EvalError> {
        let definite = sol.is_definite();
        // Resolve the variant functor BEFORE allocating into the subst arena, so
        // a missing-stdlib early-return can't strand a freshly-allocated slot.
        let functor = if definite {
            self.reflect.solution_definite
        } else {
            self.reflect.solution_undecided
        }
        .ok_or_else(|| EvalError::Internal(
            "anthill.reflect.Solution not loaded — stdlib missing the Solution enum".into(),
        ))?;
        let residual = sol.residual;
        let subst_value = Value::Substitution(self.substs.alloc(sol.subst));
        let mut named = if definite {
            vec![(self.fields.subst, subst_value)]
        } else {
            // Carrier-faithful (WI-348): the residual goals stay as their original
            // `Value`s — a goal mentioning a `Value::Node` keeps its source
            // occurrence rather than being reified to a bare `TermId` (which would
            // drop span/identity that the core deliberately preserves). Surfaced as
            // `List[Term]`: a pending goal IS a term, occurrence-carried or not, and
            // is inspected through the occurrence-aware reflect / `TermView` ops.
            let residual_list = self.build_list_value(residual, &[])?;
            vec![
                (self.fields.subst, subst_value),
                (self.fields.residual, residual_list),
            ]
        };
        // Canonical (declared) field order — mirrors `finish_constructor` — so a
        // positional pattern (`case undecided(subst, residual)`) binds the right
        // field; `subst`/`residual` are NOT in alphabetical order.
        self.kb.canonicalize_record_named_args(functor, &mut named);
        Ok(Value::Entity { functor, pos: Vec::new().into(), named: named.into() })
    }

    /// WI-714 (proposal 052 §Typing 2): materialize one resolver `Solution` onto a
    /// relation's free variables — the ONE place a relation answer becomes a value
    /// row. `columns` is `(column name, free VarId)` in the relation's declaration
    /// order; each column reads its bound value out of the answer substitution (a
    /// flat lookup by `VarId`, mirroring `Substitution.lookup`; an unbound free var
    /// carries as itself, a `Value::Var`). The row is a named-tuple `Value::Tuple`,
    /// keyed by column name (order-faithful, §4.6), 1-COLLAPSED to the element value
    /// for a single column and to `Value::Unit` for zero (a boolean/membership
    /// relation — non-empty ⇔ provable). Definite and floundered (`undecided`)
    /// answers materialize identically off `sol.subst`; NotFound is just the empty
    /// stream, no bespoke nil arm.
    fn materialize_solution(
        &mut self,
        sol: crate::kb::resolve::Solution,
        columns: &[(crate::intern::Symbol, crate::kb::term::VarId)],
    ) -> Result<Value, EvalError> {
        use crate::kb::term::Var;
        // Zero free variables → Unit (membership relation).
        if columns.is_empty() {
            return Ok(Value::Unit);
        }
        let mut named: Vec<(crate::intern::Symbol, Value)> = Vec::with_capacity(columns.len());
        for &(name, vid) in columns {
            // Read the binding through `resolve_as_value` — the single canonical
            // substitution reader (WI-348), which chases the PARENT frame chain. A
            // plain `bindings` scan would miss a binding held in a parent frame and
            // wrongly report the column unbound. The resolver binds a var to a
            // hash-consed `Value::Term`; REIFY it to a native value (scalar const →
            // scalar Value, constructor → entity) so the column reads as its element
            // sort, not a raw Term handle — a `Relation[String]` yields `Value::Str`,
            // a `Relation[Board]` an entity. An unbound free var carries as itself.
            let bound = match sol.subst.resolve_as_value(vid).cloned() {
                Some(Value::Term { id, .. }) => crate::eval::builtins::term_to_value(self, id),
                Some(v) => v,
                None => Value::Var(Var::Global(vid)),
            };
            named.push((name, bound));
        }
        // One free variable → the element value (1-collapse).
        if named.len() == 1 {
            return Ok(named.pop().unwrap().1);
        }
        // A named tuple is an ORDERED PRODUCT — its field order IS the relation
        // schema (§4.6). So, unlike `make_solution_value` (which canonicalizes a
        // Solution ENTITY into its declared field order), the row is built in
        // column / declaration order and deliberately NOT re-sorted by field name.
        Ok(Value::Tuple {
            pos: Vec::<Value>::new().into(),
            named: named.into(),
        })
    }
}
